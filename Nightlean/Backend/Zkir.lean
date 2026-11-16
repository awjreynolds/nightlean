import Nightlean.IR
import Nightlean.Backend.Impact
import Nightlean.Passes
import Nightlean.Backend.NativeExpected
import Nightlean.Backend.NativeProducer

namespace Nightlean.Backend.Zkir

open Lean

/-- Initial relation producer. Ledger transcript/state integration is separate. -/
private def nativeType : Json := toJson ("Scalar<BLS12-381>" : String)

private def validateProduced (span : SourceSpan) (expected : Native.Expected) (program : Json) :
    Except Diagnostic Json :=
  match Native.validate expected program with
  | .ok _ => .ok program
  | .error message => .error {span, message := "native producer invariant: " ++ message}

def nativeModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

private def checkConstants : Expr ty → Except String Unit
  | .native n => if n < nativeModulus then pure () else throw "noncanonical Native constant"
  | .bool _ | .ref _ => pure ()
  | .uint maximum value =>
    if maximum ≤ ScalarPolicy.maxUint && value ≤ maximum then pure ()
    else throw "noncanonical unsigned constant"
  | .add a b | .mul a b | .sub a b | .eq a b
  | .uadd a b | .usub a b | .umul a b => do checkConstants a; checkConstants b
  | .cast _ value => checkConstants value
  | .letE _ value body => do checkConstants value; checkConstants body
  | .assertE condition body => do checkConstants condition; checkConstants body
  | .disclose _ value => checkConstants value
  | .select c a b => do checkConstants c; checkConstants a; checkConstants b
  | .poseidon2 domain a b => do
    unless domain < nativeModulus do throw "noncanonical Poseidon domain tag"
    checkConstants a
    checkConstants b

private def instruction (op : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("op", toJson op) :: fields)

/-- ZKIR field immediates use little-endian bytes, including leading zero bytes. -/
def fieldImmediate (n : Nat) : String :=
  "0x" ++ go n (n.log2 / 8 + 1)
where
  go (n : Nat) : Nat → String
    | 0 => ""
    | fuel + 1 =>
      let byte := n % 256
      let digits := "0123456789abcdef".toList.toArray
      String.singleton digits[byte / 16]! ++ String.singleton digits[byte % 16]! ++
        go (n / 256) fuel

structure LowerState where
  next : Nat := 0
  instructions : Array Json := #[]
  expressions : List (String × String) := []
  aliases : List (String × String) := []

private abbrev LowerM := StateM LowerState

private def emit (op : String) (fields : List (String × Json)) : LowerM Unit :=
  modify fun s => { s with instructions := s.instructions.push (instruction op fields) }

private def fresh : LowerM String := do
  let s ← get
  set { s with next := s.next + 1 }
  return s!"%v{s.next}"

private def binary (op a b : String) : LowerM String := do
  let key := reprStr (op, a, b)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit op [("a", toJson a), ("b", toJson b), ("output", toJson output)]
  modify fun s => {s with expressions := (key, output) :: s.expressions}
  return output

private def unary (op a : String) : LowerM String := do
  let key := reprStr (op, a)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit op [("a", toJson a), ("output", toJson output)]
  modify fun s => {s with expressions := (key, output) :: s.expressions}
  return output

/-- less_than assumes bounded operands. Range-check the value first and only
compare against a constant fitting the same width. Power-of-two limits need no comparison. -/
private def constrainUnsigned (maximum : Nat) (value : String) : LowerM Unit := do
  if maximum == 0 then
    emit "constrain_eq" [("a", toJson value), ("b", toJson ("0x00" : String))]
  else
    let bits := maximum.log2 + 1
    emit "constrain_bits" [("val", toJson value), ("bits", toJson bits)]
    unless maximum + 1 == 2 ^ bits do
      let output ← fresh
      emit "less_than" [("a", toJson value), ("b", toJson (fieldImmediate (maximum + 1))),
        ("bits", toJson bits), ("output", toJson output)]
      emit "assert" [("cond", toJson output)]

private def constrainType (ty : Ty) (value : String) : LowerM Unit :=
  match ty with
  | .native => pure ()
  | .bool => emit "constrain_to_boolean" [("val", toJson value)]
  | .uint maximum => constrainUnsigned maximum value

/-- All bools use constrained Native 0/1 values, matching test_eq's result type. -/
private def lowerExpr : Expr ty → LowerM String
  | .native n => pure (fieldImmediate n)
  | .uint _ n => pure (fieldImmediate n)
  | .bool b => pure (if b then "0x01" else "0x00")
  | .ref name => do pure ((← get).aliases.lookup name |>.getD ("%input_" ++ name))
  | .add a b => do binary "add" (← lowerExpr a) (← lowerExpr b)
  | .mul a b => do binary "mul" (← lowerExpr a) (← lowerExpr b)
  | .sub a b => do binary "add" (← lowerExpr a) (← unary "neg" (← lowerExpr b))
  | .uadd (m := m) (n := n) a b => do
    let output ← binary "add" (← lowerExpr a) (← lowerExpr b)
    constrainUnsigned (m + n) output
    pure output
  | .umul (m := m) (n := n) a b => do
    let output ← binary "mul" (← lowerExpr a) (← lowerExpr b)
    constrainUnsigned (m * n) output
    pure output
  | .usub (m := m) a b => do
    let output ← binary "add" (← lowerExpr a) (← unary "neg" (← lowerExpr b))
    constrainUnsigned m output
    pure output
  | .cast target value => do
    let output ← lowerExpr value
    match target with
    | .native => pure output
    | .bool =>
      let zero ← binary "test_eq" output "0x00"
      unary "not" zero
    | .uint maximum => do
      constrainUnsigned maximum output
      pure output
  | .letE name value body => do
    let value ← lowerExpr value
    let aliases := (← get).aliases
    modify fun s => {s with aliases := (name, value) :: aliases}
    let result ← lowerExpr body
    modify fun s => {s with aliases := aliases}
    pure result
  | .assertE condition body => do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
    lowerExpr body
  | .disclose _ value => lowerExpr value
  | .eq a b => do binary "test_eq" (← lowerExpr a) (← lowerExpr b)
  | .select condition yes no => do
    let bit ← lowerExpr condition
    let a ← lowerExpr yes
    let b ← lowerExpr no
    let key := reprStr ("cond_select", bit, a, b)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "cond_select" [("bit", toJson bit), ("a", toJson a),
      ("b", toJson b), ("output", toJson output)]
    modify fun s => {s with expressions := (key, output) :: s.expressions}
    return output
  | .poseidon2 domain a b => do
    let a ← lowerExpr a
    let b ← lowerExpr b
    let key := reprStr ("transient_hash", domain, a, b)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "transient_hash" [("inputs", toJson [fieldImmediate domain, a, b]),
      ("output", toJson output)]
    modify fun s => {s with expressions := (key, output) :: s.expressions}
    return output
private def bindPublic (values : List String) : LowerM Unit :=
  emit "impact" [("guard", toJson ("0x01" : String)), ("inputs", toJson values)]

private def lowerBody (c : Circuit) : LowerM Unit := do
  for input in c.inputs do
    let output := "%input_" ++ input.name
    emit (if input.visibility == .«public» then "public_input" else "private_input")
      [("guard", Json.null), ("type", nativeType), ("output", toJson output)]
    constrainType input.ty output
    if input.visibility == .«public» then bindPublic [output]
  for condition in c.constraints do
    let value ← lowerExpr condition
    emit "assert" [("cond", toJson value)]
  let mut outputs := []
  for output in c.outputs do
    outputs := outputs ++ [← lowerExpr output.value]
  if !outputs.isEmpty then bindPublic outputs
  emit "output" [("vals", toJson outputs)]

/-- Produce a ZKIR v3.2 relation, not a deployable contract bundle.
Public values are explicitly bound with Impact. The surrounding contract must
still bind this public-input sequence to its accepted ledger call transcript. -/
def lowerCircuit (c : Circuit) : Except Diagnostic Json := do
  Disclosure.circuit c
  let c := Passes.pruneCircuit c
  c.validate { poseidon2 := true }
  for condition in c.constraints do
    match checkConstants condition with
    | .error message => throw {span := c.span, message}
    | .ok _ => pure ()
  for output in c.outputs do
    match checkConstants output.value with
    | .error message => throw {span := output.span, message}
    | .ok _ => pure ()
  let (_, result) := (lowerBody c).run {}
  let program := Json.mkObj [
    ("version", Json.mkObj [("major", toJson (3 : Nat)), ("minor", toJson (2 : Nat))]),
    ("inputs", Json.arr #[]),
    ("outputs", Json.arr (c.outputs.toArray.map fun _ => nativeType)),
    ("do_communications_commitment", toJson false),
    ("instructions", Json.arr result.instructions)]
  validateProduced c.span (← Native.expectedCircuit c) program

private def lowerEntrypointBody (entry : Entrypoint) (plan : Impact.Plan) : LowerM Unit := do
  for input in entry.circuit.inputs do
    let output := "%input_" ++ input.name
    emit (if input.visibility == .«public» then "public_input" else "private_input")
      [("guard", Json.null), ("type", nativeType), ("output", toJson output)]
    constrainType input.ty output
  for condition in entry.circuit.constraints do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
  for output in entry.circuit.outputs do
    let value ← lowerExpr output.value
    modify fun s => {s with aliases := (output.name, value) :: s.aliases}
  -- Public parameters were read above in declaration order. Remaining reads
  -- come from ledger cells and the VM membership result in transcript order.
  let publicCount := (entry.circuit.inputs.filter (·.visibility == .«public»)).length
  for read in plan.reads.drop publicCount do
    let output := "%input_" ++ read.name
    emit "public_input" [("guard", Json.null), ("type", nativeType), ("output", toJson output)]
    constrainType read.ty output
  for condition in plan.guards do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
  -- The ledger consumes one activity/skip entry per VM opcode. Flattening
  -- these groups preserves field values but breaks transaction proving.
  for operation in plan.operations do
    bindPublic (← operation.fields.mapM lowerExpr)
  -- Contract outputs are named values used in state effects. The transaction
  -- call has empty explicit return value; all disclosed values are in transcript.
  emit "output" [("vals", toJson ([] : List String))]

/-- Compile a native ledger transcript relation. Public-input binding includes
all opcode, alignment, key, read-result and write-value fields. The caller must
execute the matching Impact plan, not the standalone circuit artifact. -/
def lowerEntrypoint (state : List StateDecl) (entry : Entrypoint) : Except Diagnostic Json := do
  let entry := Passes.pruneEntrypoint entry
  let plan ← Impact.lower state entry
  let (_, result) := (lowerEntrypointBody entry plan).run {}
  let program := Json.mkObj [
    ("version", Json.mkObj [("major", toJson (3 : Nat)), ("minor", toJson (2 : Nat))]),
    ("inputs", Json.arr #[]), ("outputs", Json.arr #[]),
    -- Ledger ContractCall.public_inputs always includes the commitment after
    -- binding input. Standalone relations above deliberately keep it disabled.
    ("do_communications_commitment", toJson true),
    ("instructions", Json.arr result.instructions)]
  validateProduced entry.span (← Native.expectedEntrypoint state entry) program

end Nightlean.Backend.Zkir
