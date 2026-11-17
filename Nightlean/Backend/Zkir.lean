import Nightlean.IR
import Nightlean.Backend.Impact
import Nightlean.Passes
import Nightlean.Backend.NativeExpected
import Nightlean.Backend.NativeProducer

namespace Nightlean.Backend.Zkir

open Lean

/-- Initial relation producer. Ledger transcript/state integration is separate. -/
private def nativeType : Json := toJson ("Scalar<BLS12-381>" : String)

theorem nativeType_eq : nativeType = toJson ("Scalar<BLS12-381>" : String) := rfl

private def validateProduced (span : SourceSpan) (expected : Native.Expected) (program : Json) :
    Except Diagnostic Json :=
  match Native.validate expected program with
  | .ok _ => .ok program
  | .error message => .error {span, message := "native producer invariant: " ++ message}

theorem validateProduced_ok (span : SourceSpan) (expected : Native.Expected) (program result : Json) :
    validateProduced span expected program = .ok result ↔
      result = program ∧ Native.validate expected program = .ok () := by
  cases checked : Native.validate expected program <;> simp [validateProduced, checked]
  constructor <;> intro equal <;> exact equal.symm

private theorem bind_ok (first : Except ε α) (next : α → Except ε β) (value : β) :
    Except.bind first next = .ok value ↔ ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp [Except.bind]

def nativeModulus : Nat :=
  52435875175126190479447740508185965837690552500527637822603658699938581184513

mutual
private def checkConstants : Expr ty → Except String Unit
  | .native n => if n < nativeModulus then pure () else throw "noncanonical Native constant"
  | .bool _ | .ref _ => pure ()
  | .uint maximum value =>
    if maximum ≤ ScalarPolicy.maxUint && value ≤ maximum then pure ()
    else throw "noncanonical unsigned constant"
  | .bytesField value _ | .bytesAt value _ => checkConstants value
  | .toBytes32 value => checkConstants value
  | .fromBytes32 value => checkConstants value
  | .inv value => checkConstants value
  | .persistentHash32 value => checkConstants value
  | .bytes32Literal _ => pure ()
  | .persistentHashVector32 _ => pure ()
  | .persistentHashNative value => checkConstants value
  | .persistentHashNativeVector values => checkNativeConstants values
  | .jubjubScalarFromNative value | .jubjubScalarToNative value
  | .jubjubMulGenerator value | .jubjubNeg value
  | .jubjubCoordinate value _ => checkConstants value
  | .jubjubMul point scalar | .jubjubAdd point scalar => do
    checkConstants point
    checkConstants scalar
  | .jubjubFromCoordinates x y => do
    checkConstants x
    checkConstants y
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
termination_by value => sizeOf value
decreasing_by all_goals simp_wf <;> omega

private def checkNativeConstants : List (Expr .native) → Except String Unit
  | [] => pure ()
  | value :: rest => do
    checkConstants value
    checkNativeConstants rest
termination_by values => sizeOf values
decreasing_by all_goals simp_wf <;> omega
end

def instruction (op : String) (fields : List (String × Json)) : Json :=
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

/-- CSE compares actual opcode, ordered operands and optional hash domain.
Structural keys make cache-hit meaning available to kernel proofs. -/
abbrev ExpressionKey := String × List String × Option Nat

structure LowerState where
  next : Nat := 0
  instructions : Array Json := #[]
  expressions : List (ExpressionKey × String) := []
  aliases : List (String × String) := []
  byteAliases : List (String × List String) := []
  pointCoordinates : List (String × (String × String)) := []

private abbrev LowerM := StateM LowerState

def emit (op : String) (fields : List (String × Json)) : LowerM Unit :=
  modify fun s => { s with instructions := s.instructions.push (instruction op fields) }

/-- Keep the state-only lowering monad total while ensuring rejected source
shapes still fail the mandatory native validator. -/
-- shortcut: replace validator poison with typed lowering errors when extending byte expressions.
private def rejectLowering (message : String) : LowerM Unit :=
  emit "nightlean_invalid_lowering" [("message", toJson message)]

def fresh : LowerM String := do
  let s ← get
  set { s with next := s.next + 1 }
  return s!"%v{s.next}"

def binary (op a b : String) : LowerM String := do
  let key : ExpressionKey := (op, [a, b], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit op [("a", toJson a), ("b", toJson b), ("output", toJson output)]
  modify fun s => {s with expressions := (key, output) :: s.expressions}
  return output

def unary (op a : String) : LowerM String := do
  let key : ExpressionKey := (op, [a], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit op [("a", toJson a), ("output", toJson output)]
  modify fun s => {s with expressions := (key, output) :: s.expressions}
  return output

/-- less_than assumes bounded operands. Range-check the value first and only
compare against a constant fitting the same width. Power-of-two limits need no comparison. -/
def constrainUnsigned (maximum : Nat) (value : String) : LowerM Unit := do
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

def constrainType (ty : Ty) (value : String) : LowerM Unit :=
  match ty with
  | .native => pure ()
  | .bool => emit "constrain_to_boolean" [("val", toJson value)]
  | .uint maximum => constrainUnsigned maximum value
  | .bytes _ => rejectLowering "Bytes32 must be expanded into byte inputs"
  | .jubjubScalar | .jubjubPoint => rejectLowering "Jubjub values require their typed input bridge"

private def lowerJubjubScalarFromNative (native : String) : LowerM String := do
  let key : ExpressionKey := ("jubjub_scalar_from_native", [native], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit "jubjub_scalar_from_native" [("native", toJson native), ("output", toJson output)]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def lowerJubjubScalarToNative (scalar : String) : LowerM String := do
  let key : ExpressionKey := ("encode_jubjub_scalar", [scalar], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit "encode" [("input", toJson scalar), ("outputs", toJson [output])]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def lowerPointCoordinates (point : String) : LowerM (String × String) := do
  if let some outputs := (← get).pointCoordinates.lookup point then return outputs
  let x ← fresh
  let y ← fresh
  emit "into_coordinates" [("point", toJson point), ("outputs", toJson [x, y])]
  modify fun state => {state with pointCoordinates := (point, (x, y)) :: state.pointCoordinates}
  pure (x, y)

/-- Every coordinate reconstruction checks both affine limbs after the pinned
FromCoordinates operation. This closes the source/native x roundtrip gap. -/
private def lowerPointFromCoordinates (x y : String) : LowerM String := do
  let key : ExpressionKey := ("from_coordinates_jubjub", [x, y], none)
  let point ← match (← get).expressions.lookup key with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "from_coordinates" [("inputs", toJson [x, y]), ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  let (actualX, actualY) ← lowerPointCoordinates point
  emit "constrain_eq" [("a", toJson x), ("b", toJson actualX)]
  emit "constrain_eq" [("a", toJson y), ("b", toJson actualY)]
  pure point

private def packBytes : List String → LowerM String
  | [] => pure "0x00"
  | byte :: rest => do
    let suffix ← packBytes rest
    let scaled ← binary "mul" "0x0001" suffix
    binary "add" byte scaled

private def bytes32Alignment : Json := Json.arr #[Json.mkObj [
  ("tag", toJson ("atom" : String)),
  ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson (32 : Nat))])]]

private def bytes32Atom : Json := Json.mkObj [
  ("tag", toJson ("atom" : String)),
  ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson (32 : Nat))])]

private def bytes32VectorAlignment (length : Nat) : Json :=
  Json.arr ((List.replicate length bytes32Atom).toArray)

private def nativeFieldAtom : Json := Json.mkObj [
  ("tag", toJson ("atom" : String)),
  ("value", Json.mkObj [("tag", toJson ("field" : String))])]

private def nativeFieldAlignment : Json := Json.arr #[nativeFieldAtom]

private def nativeFieldVectorAlignment (length : Nat) : Json :=
  Json.arr ((List.replicate length nativeFieldAtom).toArray)

/-- Emit/reuse one typed aligned SHA-256 operation and its modern Encode outputs.
The key includes the preimage kind, so identical field strings under different
FAB alignments never share a digest. The returned chunks use Encode order. -/
private def lowerPersistentHash (preimageKind : String) (alignment : Json)
    (operands : List String) : LowerM (List String) := do
  let hashKey : ExpressionKey := ("persistent_hash:" ++ preimageKind, operands, none)
  let hashOutput ← match (← get).expressions.lookup hashKey with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "persistent_hash" [
        ("alignment", alignment),
        ("inputs", toJson operands),
        ("output", toJson output)]
      modify fun state => {state with expressions := (hashKey, output) :: state.expressions}
      pure output
  let lowKey : ExpressionKey := ("encode_bytes32", [hashOutput], some 0)
  let highKey : ExpressionKey := ("encode_bytes32", [hashOutput], some 1)
  match ((← get).expressions.lookup lowKey, (← get).expressions.lookup highKey) with
  | (some low, some high) => pure [low, high]
  | _ => do
    let low ← fresh
    let high ← fresh
    emit "encode" [("input", toJson hashOutput), ("outputs", toJson [low, high])]
    modify fun state => {state with expressions :=
      (lowKey, low) :: (highKey, high) :: state.expressions}
    pure [low, high]

private def encodeBytes32 (bytes : String) : LowerM (String × String) := do
  let lowKey : ExpressionKey := ("encode_bytes32", [bytes], some 0)
  let highKey : ExpressionKey := ("encode_bytes32", [bytes], some 1)
  match ((← get).expressions.lookup lowKey, (← get).expressions.lookup highKey) with
  | (some low, some high) => pure (low, high)
  | _ => do
    let low ← fresh
    let high ← fresh
    emit "encode" [("input", toJson bytes), ("outputs", toJson [low, high])]
    modify fun state => {state with expressions :=
      (lowKey, low) :: (highKey, high) :: state.expressions}
    pure (low, high)

private def encodeByte (byte : String) : LowerM String := do
  let key : ExpressionKey := ("encode_byte", [byte], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit "encode" [("input", toJson byte), ("outputs", toJson [output])]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def lowerToBytes32 (value : String) : LowerM (String × String) := do
  let bytesKey : ExpressionKey := ("to_bytes", [value], none)
  let bytes ← match (← get).expressions.lookup bytesKey with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "to_bytes" [("input", toJson value), ("output", toJson output)]
      modify fun state => {state with expressions := (bytesKey, output) :: state.expressions}
      pure output
  encodeBytes32 bytes

private def bytes32Chunks (values : List String) : LowerM (String × String) := do
  match values.length with
  | 2 => pure (values[0]!, values[1]!)
  | 32 => pure (← packBytes (values.take 31), values[31]!)
  | _ => do
    rejectLowering "Bytes32 source has wrong aligned encoding"
    pure ("0x00", "0x00")

private def lowerBytesFromChunks (low31 highByte : String) : LowerM String := do
  let key : ExpressionKey := ("bytes_from_natives", [low31, highByte], some 32)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← fresh
  emit "bytes_from_natives" [
    ("inputs", toJson [low31, highByte]),
    ("len", toJson (32 : Nat)),
    ("output", toJson output)]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private def lowerComputedBytes32ByteAt (values : List String) (index : Nat) : LowerM String := do
  if index ≥ 32 then do
    rejectLowering "Bytes32 byte index is out of range"
    pure "0x00"
  else do
    let (low31, highByte) ← bytes32Chunks values
    let bytes ← lowerBytesFromChunks low31 highByte
    let key : ExpressionKey := ("nth", [bytes], some index)
    let byte ← match (← get).expressions.lookup key with
      | some existing => pure existing
      | none => do
        let output ← fresh
        emit "nth" [("bytes", toJson bytes), ("index", toJson index), ("output", toJson output)]
        modify fun state => {state with expressions := (key, output) :: state.expressions}
        pure output
    encodeByte byte

private def nativeTypeName : Ty → String
  | .native => "Scalar<BLS12-381>"
  | .jubjubScalar => "Scalar<Jubjub>"
  | .jubjubPoint => "Point<Jubjub>"
  | _ => "Unsupported"

private def lowerFromBytes32 (target : Ty) (values : List String) : LowerM String := do
  let (low31, highByte) ← bytes32Chunks values
  let bytes ← lowerBytesFromChunks low31 highByte
  let typeName := nativeTypeName target
  let key : ExpressionKey := ("from_bytes:" ++ typeName, [bytes], none)
  let output ← match (← get).expressions.lookup key with
    | some existing => pure existing
    | none => do
      let output ← fresh
      emit "from_bytes" [
        ("bytes", toJson bytes),
        ("type", toJson typeName),
        ("output", toJson output)]
      modify fun state => {state with expressions := (key, output) :: state.expressions}
      pure output
  if target == .jubjubPoint then do
    let (roundtripLow, roundtripHigh) ← lowerToBytes32 output
    let highEq ← binary "test_eq" highByte roundtripHigh
    emit "assert" [("cond", toJson highEq)]
    let lowEq ← binary "test_eq" low31 roundtripLow
    emit "assert" [("cond", toJson lowEq)]
  pure output

private def alignedBytes32Fields (values : List String) : LowerM (String × String) := do
  match values.length with
  | 32 =>
    let low31 ← packBytes (values.take 31)
    pure (values[31]!, low31)
  | 2 => pure (values[1]!, values[0]!)
  | _ => do
    rejectLowering "Bytes32 source has wrong aligned encoding"
    pure ("0x00", "0x00")

private def lowerByteInput (input : Input) : LowerM Unit := do
  match input.ty with
  | .bytes _ =>
    let identifiers := input.nativeIdentifiers
    for output in identifiers do
      emit (if input.visibility == .«public» then "public_input" else "private_input")
        [("guard", Json.null), ("type", nativeType), ("output", toJson output)]
      constrainUnsigned 255 output
    modify fun state => {state with byteAliases := (input.name, identifiers) :: state.byteAliases}
  | .jubjubScalar => do
    let native := input.nativeIdentifiers.head!
    emit (if input.visibility == .«public» then "public_input" else "private_input")
      [("guard", Json.null), ("type", nativeType), ("output", toJson native)]
    let scalar ← lowerJubjubScalarFromNative native
    let encoded ← lowerJubjubScalarToNative scalar
    emit "constrain_eq" [("a", toJson native), ("b", toJson encoded)]
    modify fun state => {state with aliases := (input.name, scalar) :: state.aliases}
  | .jubjubPoint => do
    let x := input.nativeIdentifiers[0]!
    let y := input.nativeIdentifiers[1]!
    for identifier in [x, y] do
      emit (if input.visibility == .«public» then "public_input" else "private_input")
        [("guard", Json.null), ("type", nativeType), ("output", toJson identifier)]
    let point ← lowerPointFromCoordinates x y
    modify fun state => {state with aliases := (input.name, point) :: state.aliases}
  | _ =>
    let output := input.nativeIdentifiers.head!
    emit (if input.visibility == .«public» then "public_input" else "private_input")
      [("guard", Json.null), ("type", nativeType), ("output", toJson output)]
    constrainType input.ty output

mutual
private def lowerBytes : Expr (.bytes length) → LowerM (List String)
  | .ref name => do
    match (← get).byteAliases.lookup name with
    | some values => pure values
    | none =>
      rejectLowering s!"unbound Bytes32 source symbol '{name}'"
      pure []
  | .disclose _ value => lowerBytes value
  | .bytes32Literal values => pure (values.map fieldImmediate)
  | .persistentHash32 value => do
    let values ← lowerBytes value
    let (highByte, low31) ← alignedBytes32Fields values
    lowerPersistentHash "bytes32" bytes32Alignment [highByte, low31]
  | .persistentHashVector32 values => do
    let operands ← lowerBytes32VectorFields values
    if values.length == 1 then
      lowerPersistentHash "bytes32" bytes32Alignment operands
    else
      lowerPersistentHash ("bytes32-vector:" ++ toString values.length)
        (bytes32VectorAlignment values.length) operands
  | .persistentHashNative value => do
    let native ← lowerExpr value
    lowerPersistentHash "native-field" nativeFieldAlignment [native]
  | .persistentHashNativeVector values => do
    let operands ← lowerNativeVectorFields values
    if values.length == 1 then
      lowerPersistentHash "native-field" nativeFieldAlignment operands
    else
      lowerPersistentHash ("native-field-vector:" ++ toString values.length)
        (nativeFieldVectorAlignment values.length) operands
  | .toBytes32 value => do
    let input ← lowerExpr value
    let (low, high) ← lowerToBytes32 input
    pure [low, high]
  | .select condition yes no => do
    let condition ← lowerExpr condition
    let (yesLow, yesHigh) ← bytes32Chunks (← lowerBytes yes)
    let (noLow, noHigh) ← bytes32Chunks (← lowerBytes no)
    let low ← fresh
    emit "cond_select" [("bit", toJson condition), ("a", toJson yesLow),
      ("b", toJson noLow), ("output", toJson low)]
    let high ← fresh
    emit "cond_select" [("bit", toJson condition), ("a", toJson yesHigh),
      ("b", toJson noHigh), ("output", toJson high)]
    pure [low, high]
  | @Expr.letE (.bytes _) _ name value body => do
    let values ← lowerBytes value
    let aliases := (← get).byteAliases
    modify fun state => {state with byteAliases := (name, values) :: aliases}
    let result ← lowerBytes body
    modify fun state => {state with byteAliases := aliases}
    pure result
  | @Expr.letE _ _ name value body => do
    let value ← lowerExpr value
    let aliases := (← get).aliases
    modify fun state => {state with aliases := (name, value) :: aliases}
    let result ← lowerBytes body
    modify fun state => {state with aliases}
    pure result
  | .assertE condition body => do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
    lowerBytes body
  | _ => do
    rejectLowering "unsupported Bytes32 expression in native lowering"
    pure []
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf <;> omega

private def lowerBytes32VectorFields : List (Expr (.bytes 32)) → LowerM (List String)
  | [] => pure []
  | value :: rest => do
    let bytes ← lowerBytes value
    let (highByte, low31) ← alignedBytes32Fields bytes
    pure ([highByte, low31] ++ (← lowerBytes32VectorFields rest))
termination_by values => sizeOf values
decreasing_by
  all_goals simp_wf <;> omega

private def lowerNativeVectorFields : List (Expr .native) → LowerM (List String)
  | [] => pure []
  | value :: rest => do
    let first ← lowerExpr value
    pure (first :: (← lowerNativeVectorFields rest))
termination_by values => sizeOf values
decreasing_by
  all_goals simp_wf <;> omega

/-- All bools use constrained Native 0/1 values, matching test_eq's result type. -/
def lowerExpr : Expr ty → LowerM String
  | .native n => pure (fieldImmediate n)
  | .uint _ n => pure (fieldImmediate n)
  | .bool b => pure (if b then "0x01" else "0x00")
  | .ref name => do
    match ty with
    | .bytes _ => do
      rejectLowering "Bytes32 cannot be used as a scalar expression"
      pure "0x00"
    | .jubjubScalar | .jubjubPoint =>
      match (← get).aliases.lookup name with
      | some value => pure value
      | none => do
        rejectLowering "unbound typed Jubjub source symbol"
        pure "0x00"
    | _ => pure ((← get).aliases.lookup name |>.getD ("%input_" ++ name))
  | .bytesField value index => do
    let values ← lowerBytes value
    match values.length, index with
    | 2, 0 => pure values[1]!
    | 2, 1 => pure values[0]!
    | 32, 0 => packBytes (values.drop 31)
    | 32, 1 => packBytes (values.take 31)
    | _, _ => do
      rejectLowering "Bytes32 source or field chunk index has an invalid encoding"
      pure "0x00"
  | .bytesAt value index => do
    let values ← lowerBytes value
    if values.length == 2 then
      lowerComputedBytes32ByteAt values index
    else if values.length != 32 then
      rejectLowering "Bytes32 source has wrong byte count"
      pure "0x00"
    else
      match values[index]? with
      | some byte => pure byte
      | none =>
        rejectLowering "Bytes32 byte index is out of range"
        pure "0x00"
  | .jubjubScalarFromNative value => do
    lowerJubjubScalarFromNative (← lowerExpr value)
  | .jubjubScalarToNative value => do
    lowerJubjubScalarToNative (← lowerExpr value)
  | .jubjubMulGenerator scalar => do
    let scalar ← lowerExpr scalar
    let key : ExpressionKey := ("ec_mul_generator", [scalar], none)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "ec_mul_generator" [("scalar", toJson scalar), ("output", toJson output)]
    modify fun state => {state with expressions := (key, output) :: state.expressions}
    pure output
  | .jubjubMul point scalar => do
    let point ← lowerExpr point
    let scalar ← lowerExpr scalar
    let key : ExpressionKey := ("ec_mul", [point, scalar], none)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "ec_mul" [("a", toJson point), ("scalar", toJson scalar), ("output", toJson output)]
    modify fun state => {state with expressions := (key, output) :: state.expressions}
    pure output
  | .jubjubAdd left right => do
    binary "add" (← lowerExpr left) (← lowerExpr right)
  | .jubjubNeg point => do unary "neg" (← lowerExpr point)
  | .jubjubCoordinate point index => do
    let point ← lowerExpr point
    let (x, y) ← lowerPointCoordinates point
    match index with
    | 0 => pure x
    | 1 => pure y
    | _ => do
      rejectLowering "Jubjub coordinate index must be 0 or 1"
      pure "0x00"
  | .jubjubFromCoordinates x y => do
    lowerPointFromCoordinates (← lowerExpr x) (← lowerExpr y)
  | .fromBytes32 value => do
    let values ← lowerBytes value
    lowerFromBytes32 ty values
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
  | .inv value => do
    let operand ← lowerExpr value
    let nonzeroOperand ← match ty with
      | .native => pure operand
      | .jubjubScalar => lowerJubjubScalarToNative operand
      | _ => do
        rejectLowering "inv supports only Native and JubjubScalar values"
        pure operand
    let isZero ← binary "test_eq" nonzeroOperand "0x00"
    let isNonzero ← unary "not" isZero
    emit "assert" [("cond", toJson isNonzero)]
    unary "inv" operand
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
    | .bytes _ => do
      rejectLowering "byte strings do not support scalar casts"
      pure "0x00"
    | .jubjubScalar | .jubjubPoint => do
      rejectLowering "Jubjub values do not support generic scalar casts"
      pure "0x00"
  | @Expr.letE (.bytes _) _ name value body => do
    let value ← lowerBytes value
    let byteAliases := (← get).byteAliases
    modify fun state => {state with byteAliases := (name, value) :: byteAliases}
    let result ← lowerExpr body
    modify fun state => {state with byteAliases}
    pure result
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
    let key : ExpressionKey := ("cond_select", [bit, a, b], none)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "cond_select" [("bit", toJson bit), ("a", toJson a),
      ("b", toJson b), ("output", toJson output)]
    modify fun s => {s with expressions := (key, output) :: s.expressions}
    return output
  | .poseidon2 domain a b => do
    let a ← lowerExpr a
    let b ← lowerExpr b
    let key : ExpressionKey := ("transient_hash", [a, b], some domain)
    if let some existing := (← get).expressions.lookup key then return existing
    let output ← fresh
    emit "transient_hash" [("inputs", toJson [fieldImmediate domain, a, b]),
      ("output", toJson output)]
    modify fun s => {s with expressions := (key, output) :: s.expressions}
    return output
  | .bytes32Literal _ | .persistentHash32 _ | .persistentHashVector32 _
  | .persistentHashNative _ | .persistentHashNativeVector _ | .toBytes32 _ => do
    rejectLowering "Bytes32 expressions must be consumed with their typed FAB alignment"
    pure "0x00"
termination_by value => sizeOf value
decreasing_by
  all_goals simp_wf <;> omega
end
def bindPublic (values : List String) : LowerM Unit :=
  emit "impact" [("guard", toJson ("0x01" : String)), ("inputs", toJson values)]

def bindPublicGuarded (guard : Expr .bool) (values : List String) : LowerM Unit := do
  emit "impact" [("guard", toJson (← lowerExpr guard)), ("inputs", toJson values)]

def lowerBody (c : Circuit) : LowerM Unit := do
  for input in c.inputs do
    lowerByteInput input
    if input.visibility == .«public» then
      for output in input.nativeIdentifiers do bindPublic [output]
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
private def loweringCapabilities : Capabilities :=
  { poseidon2 := true, persistentHash32 := true,
    persistentHashVector32 := true, persistentHashNative := true,
    bytes32Conversions := true, jubjub := true }

def lowerCircuit (c : Circuit) : Except Diagnostic Json := do
  Disclosure.circuit c
  let c := Passes.pruneCircuit c
  c.validate loweringCapabilities
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

/-- Successful lowering necessarily passes the existing mandatory validation
against the independently reconstructed statement of the actual pruned source. -/
theorem lowerCircuit_validated (circuit : Circuit) (program : Json)
    (accepted : lowerCircuit circuit = .ok program) :
    ∃ expected, Native.expectedCircuit (Passes.pruneCircuit circuit) = .ok expected ∧
      Native.validate expected program = .ok () := by
  simp only [lowerCircuit, bind, bind_ok] at accepted
  rcases accepted with ⟨_, disclosure, _, validation, _, constants, _, outputConstants, gate⟩
  cases produced : (lowerBody (Passes.pruneCircuit circuit)).run {} with
  | mk value state =>
    simp only [produced] at gate
    rw [bind_ok] at gate
    rcases gate with ⟨expected, expectedAccepted, producerAccepted⟩
    obtain ⟨equal, checked⟩ := (validateProduced_ok _ _ _ _).mp producerAccepted
    exact ⟨expected, expectedAccepted, by rw [equal]; exact checked⟩

/-- Relate the accepted JSON instruction vector to the actual lowerBody run. -/
theorem lowerCircuit_instructions (circuit : Circuit) (program : Json)
    (accepted : lowerCircuit circuit = .ok program) :
    Native.arrayField program "instructions" =
      .ok ((lowerBody (Passes.pruneCircuit circuit)).run {}).2.instructions := by
  simp only [lowerCircuit, bind, bind_ok] at accepted
  rcases accepted with ⟨_, disclosure, _, validation, _, constants, _, outputConstants, gate⟩
  cases produced : (lowerBody (Passes.pruneCircuit circuit)).run {} with
  | mk value state =>
    simp only [produced] at gate
    rw [bind_ok] at gate
    rcases gate with ⟨expected, expectedAccepted, producerAccepted⟩
    obtain ⟨equal, checked⟩ := (validateProduced_ok _ _ _ _).mp producerAccepted
    rw [equal]
    rfl

def lowerEntrypointBody (entry : Entrypoint) (plan : Impact.Plan) : LowerM Unit := do
  for input in entry.circuit.inputs do
    lowerByteInput input
  for condition in entry.circuit.constraints do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
  for output in entry.circuit.outputs do
    let value ← lowerExpr output.value
    modify fun s => {s with aliases := (output.name, value) :: s.aliases}
  -- Public parameters were read above in declaration order. Remaining reads
  -- come from ledger cells and the VM membership result in transcript order.
  let publicCount := Impact.publicInputReadCount entry.circuit.inputs
  for read in plan.reads.drop publicCount do
    let activity ← match read.guard with
      | none => pure Json.null
      | some guard => pure (toJson (← lowerExpr guard))
    for (name, ty) in read.bindings do
      let output := "%input_" ++ name
      emit "public_input" [("guard", activity), ("type", nativeType), ("output", toJson output)]
      constrainType ty output
    for condition in read.inactiveDefaultConstraints do
      emit "assert" [("cond", toJson (← lowerExpr condition))]
  for condition in plan.guards do
    emit "assert" [("cond", toJson (← lowerExpr condition))]
  -- The ledger consumes one activity/skip entry per VM opcode. Flattening
  -- these groups preserves field values but breaks transaction proving.
  for (operation, index) in plan.operations.zipIdx do
    let guard := ((plan.activityGuards[index]?).getD none).getD (.bool true)
    bindPublicGuarded guard (← operation.fields.mapM lowerExpr)
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

/-- Accepted ledger-call JSON retains the exact instruction vector emitted by
the production body over the actual accepted pruned plan. -/
theorem lowerEntrypoint_instructions (state : List StateDecl) (entry : Entrypoint)
    (program : Json) (accepted : lowerEntrypoint state entry = .ok program) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Native.arrayField program "instructions" =
        .ok ((lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions := by
  simp only [lowerEntrypoint, bind, bind_ok] at accepted
  rcases accepted with ⟨plan, lowered, gate⟩
  cases produced : (lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {} with
  | mk value result =>
    simp only [produced] at gate
    rw [bind_ok] at gate
    rcases gate with ⟨expected, _, producerAccepted⟩
    obtain ⟨equal, _⟩ := (validateProduced_ok _ _ _ _).mp producerAccepted
    refine ⟨plan, lowered, ?_⟩
    rw [equal, produced]
    rfl

end Nightlean.Backend.Zkir
