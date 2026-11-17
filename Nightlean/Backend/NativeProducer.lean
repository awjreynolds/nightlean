import Nightlean.Backend.Native
import Nightlean.Backend.NativeMeaning
import Lean

namespace Nightlean.Backend.Native
open Lean

def maxInstructions : Nat := 4096
def maxVectorLength : Nat := 4096
def maxSymbolicNodes : Nat := 65536
def maxSymbolicDepth : Nat := 256

def ensure (condition : Bool) (message : String) : Except String Unit :=
  if condition then pure () else throw message

private def objectFields (value : Json) : Except String (List String) := do
  pure ((← value.getObj?).toList.map Prod.fst)

private def fields (value : Json) (expected : List String) : Except String Unit := do
  let actual ← objectFields value
  ensure (actual.length == expected.length && actual.eraseDups.length == actual.length &&
    actual.all expected.contains && expected.all actual.contains)
    "missing, unknown or mismatched native instruction fields"

def stringField (value : Json) (name : String) : Except String String := do
  (← value.getObjVal? name).getStr?

def arrayField (value : Json) (name : String) : Except String (Array Json) := do
  (← value.getObjVal? name).getArr?

def natField (value : Json) (name : String) : Except String Nat := do
  let item ← value.getObjVal? name
  let number ← item.getNat?
  ensure (item.compress == toString number) "native integer metadata must use canonical natural JSON numbers"
  pure number

def hexDigit (value : Char) : Option Nat :=
  if '0' ≤ value && value ≤ '9' then some (value.toNat - '0'.toNat)
  else if 'a' ≤ value && value ≤ 'f' then some (value.toNat - 'a'.toNat + 10)
  else none

def hexBytes : List Char → Option (List Nat)
  | [] => some []
  | high :: low :: rest => do
    let high ← hexDigit high
    let low ← hexDigit low
    pure ((high * 16 + low) :: (← hexBytes rest))
  | _ => none

def littleEndian : List Nat → Nat
  | [] => 0
  | first :: rest => first + 256 * littleEndian rest

/-- Exactly the canonical little-endian field syntax emitted by this producer. -/
def immediate (text : String) : Except String Nat := do
  ensure (text.startsWith "0x") "native immediate must start with lowercase 0x"
  let some bytes := hexBytes (text.toList.drop 2) | throw "invalid native hexadecimal immediate"
  ensure (!bytes.isEmpty && bytes.length ≤ 32) "native immediate has an invalid byte width"
  ensure (bytes.length == 1 || bytes.getLast? != some 0) "nonminimal native immediate"
  let number := littleEndian bytes
  ensure (number < Field.modulus) "noncanonical native field immediate"
  pure number

private def validIdentifier (name : String) : Bool :=
  name.startsWith "%" && name.length > 1 && name.utf8ByteSize ≤ 1024

inductive NativeValueType where
  | native | bytes32
  deriving Repr, BEq, DecidableEq

structure Fact where
  term : Term
  maximum : Nat
  valueType : NativeValueType := .native
  nodes : Nat := 1
  depth : Nat := 1
  assertedLessThan : Option (String × Nat) := none
  deriving Repr

structure State where
  definitions : List (String × Fact) := []
  inputCount : Nat := 0
  groupCount : Nat := 0
  assertionCount : Nat := 0

def combine (term : Term) (maximum : Nat) (children : List Fact) : Except String Fact := do
  let nodes := 1 + (children.map (·.nodes)).sum
  let depth := 1 + (children.map (·.depth)).foldl max 0
  ensure (nodes ≤ maxSymbolicNodes && depth ≤ maxSymbolicDepth) "native symbolic expression resource limit exceeded"
  pure {term, maximum, nodes, depth}

def operand (state : State) (text : String) : Except String Fact := do
  if text.startsWith "0x" then
    let value ← immediate text
    pure {term := .constant value, maximum := value}
  else
    ensure (validIdentifier text) "invalid native SSA reference"
    let some fact := state.definitions.lookup text | throw s!"native use before definition: {text}"
    pure fact

private def requireNative (fact : Fact) : Except String Unit :=
  ensure (fact.valueType == .native) "native instruction operand must have Native type"

private def nativeOperand (state : State) (text : String) : Except String Fact := do
  let fact ← operand state text
  requireNative fact
  pure fact

def argument (state : State) (instruction : Json) (name : String) : Except String Fact := do
  operand state (← stringField instruction name)

private def nativeArgument (state : State) (instruction : Json) (name : String) : Except String Fact := do
  nativeOperand state (← stringField instruction name)

def define (state : State) (name : String) (fact : Fact) : Except String State := do
  ensure (validIdentifier name) "invalid native SSA definition"
  ensure ((state.definitions.lookup name).isNone) s!"duplicate native SSA definition: {name}"
  pure {state with definitions := state.definitions ++ [(name, fact)]}

def defineResult (state : State) (instruction : Json) (fact : Fact) : Except String State := do
  define state (← stringField instruction "output") fact

def refine (state : State) (text : String) (maximum : Nat) : Except String State := do
  let fact ← operand state text
  requireNative fact
  if text.startsWith "%" then
    pure {state with definitions := state.definitions.map fun (name, value) =>
      (name, if name == text then {value with maximum := min value.maximum maximum} else value)}
  else
    ensure (fact.maximum ≤ maximum) "constant violates native range/equality constraint"
    pure state

def requireBoolean (fact : Fact) : Except String Unit :=
  ensure (fact.maximum ≤ 1) "native Boolean precondition is not established"

def width (instruction : Json) : Except String Nat := do
  let bits ← natField instruction "bits"
  ensure (0 < bits && bits ≤ ScalarPolicy.maxBits) "unsupported native bit width"
  pure bits

def arguments (state : State) (instruction : Json) (name : String) : Except String (List Fact) := do
  let values ← arrayField instruction name
  ensure (values.size ≤ maxVectorLength) "native operand vector resource limit exceeded"
  values.toList.mapM fun item => do operand state (← item.getStr?)

private def nativeArguments (state : State) (instruction : Json) (name : String) : Except String (List Fact) := do
  let values ← arguments state instruction name
  values.forM requireNative
  pure values

private def nativeType (value : Json) : Except String Unit := do
  ensure ((← value.getStr?) == "Scalar<BLS12-381>") "unsupported native value type/encoding"

private def bytes32Alignment : Json := Json.arr #[Json.mkObj [
  ("tag", toJson ("atom" : String)),
  ("value", Json.mkObj [("tag", toJson ("bytes" : String)), ("length", toJson (32 : Nat))])]]

def validateInstruction (expected : Expected) (state : State) (instruction : Json) : Except String State := do
  let opcode ← stringField instruction "op"
  let descriptor ← requireInstruction opcode
  fields instruction ("op" :: descriptor.fields)
  match opcode with
  | "public_input" | "private_input" =>
    nativeType (← instruction.getObjVal? "type")
    let some required := expected.inputs[state.inputCount]? | throw "unexpected native transcript input"
    match required.activityGuard with
    | none =>
      ensure ((← instruction.getObjVal? "guard") == Json.null)
        "unexpected native input activity guard"
    | some expectedGuard =>
      ensure (expected.mode == .ledgerCall && opcode == "public_input" &&
        required.visibility == .«public»)
        "conditional inputs require a source-bound public ledger read"
      let guard ← nativeOperand state (← stringField instruction "guard")
      requireBoolean guard
      ensure (guard.term == expectedGuard) "native read activity guard mismatch"
    let output ← stringField instruction "output"
    ensure (output == required.identifier &&
      opcode == (if required.visibility == .«public» then "public_input" else "private_input"))
      "native transcript input schema/order mismatch"
    let state ← define state output {term := .input output, maximum := Field.modulus - 1}
    pure {state with inputCount := state.inputCount + 1}
  | "add" | "mul" | "test_eq" =>
    let left ← nativeArgument state instruction "a"
    let right ← nativeArgument state instruction "b"
    let maximum := if opcode == "test_eq" then 1 else
      let bound := if opcode == "add" then left.maximum + right.maximum else left.maximum * right.maximum
      if bound < Field.modulus then bound else Field.modulus - 1
    defineResult state instruction (← combine (.binary opcode left.term right.term) maximum [left, right])
  | "neg" | "not" =>
    let value ← nativeArgument state instruction "a"
    if opcode == "not" then requireBoolean value
    let maximum := if opcode == "not" then 1 else if value.maximum == 0 then 0 else Field.modulus - 1
    defineResult state instruction (← combine (.unary opcode value.term) maximum [value])
  | "cond_select" =>
    let condition ← nativeArgument state instruction "bit"
    requireBoolean condition
    let yes ← nativeArgument state instruction "a"
    let no ← nativeArgument state instruction "b"
    defineResult state instruction (← combine (.select condition.term yes.term no.term)
      (max yes.maximum no.maximum) [condition, yes, no])
  | "constrain_to_boolean" => refine state (← stringField instruction "val") 1
  | "constrain_bits" =>
    refine state (← stringField instruction "val") (2 ^ (← width instruction) - 1)
  | "constrain_eq" =>
    let leftText ← stringField instruction "a"
    let rightText ← stringField instruction "b"
    let left ← nativeOperand state leftText
    let right ← nativeOperand state rightText
    let maximum := min left.maximum right.maximum
    let state ← refine state leftText maximum
    refine state rightText maximum
  | "less_than" =>
    let leftText ← stringField instruction "a"
    let left ← nativeOperand state leftText
    let right ← nativeArgument state instruction "b"
    let bits ← width instruction
    ensure (left.maximum < 2 ^ bits && right.maximum < 2 ^ bits)
      "less_than operand range precondition is not established"
    let fact ← combine (.binary s!"less_than:{bits}" left.term right.term) 1 [left, right]
    let assumption := match right.term with
      | .constant bound => if leftText.startsWith "%" then some (leftText, bound) else none
      | _ => none
    defineResult state instruction {fact with assertedLessThan := assumption}
  | "assert" =>
    let value ← nativeArgument state instruction "cond"
    requireBoolean value
    let state := if expected.assertions[state.assertionCount]? == some value.term then
      {state with assertionCount := state.assertionCount + 1} else state
    if let some (identifier, exclusive) := value.assertedLessThan then
      ensure (exclusive > 0) "asserted less_than has an impossible zero bound"
      refine state identifier (exclusive - 1)
    else pure state
  | "persistent_hash" => do
    let alignment ← instruction.getObjVal? "alignment"
    ensure (alignment == bytes32Alignment) "persistent_hash requires the exact Bytes32 FAB alignment"
    let values ← nativeArguments state instruction "inputs"
    let (highByte, low31) ← match values with
      | [highByte, low31] => pure (highByte, low31)
      | _ => throw "Bytes32 persistent_hash requires exactly two aligned field operands"
    ensure (values.all (·.valueType == .native)) "persistent_hash operands must be native fields"
    ensure (highByte.maximum ≤ 255 && low31.maximum ≤ 2 ^ (31 * 8) - 1)
      "Bytes32 persistent_hash operands lack byte-aligned range constraints"
    let fact ← combine (persistentHash32Term highByte.term low31.term)
      (Field.modulus - 1) values
    let output ← stringField instruction "output"
    define state output {fact with valueType := .bytes32}
  | "encode" => do
    let input ← argument state instruction "input"
    ensure (input.valueType == .bytes32)
      "encode in this source package accepts only a typed persistent_hash Bytes32 result"
    let outputs ← arrayField instruction "outputs"
    ensure (outputs.size == 2) "Bytes32 encode requires exactly two native outputs"
    let lowName ← outputs[0]!.getStr?
    let highName ← outputs[1]!.getStr?
    let low ← combine (encodedHashChunkTerm input.term 0) (2 ^ (31 * 8) - 1) [input]
    let state ← define state lowName low
    let high ← combine (encodedHashChunkTerm input.term 1) 255 [input]
    define state highName high
  | "transient_hash" =>
    let values ← nativeArguments state instruction "inputs"
    ensure (!values.isEmpty) "empty native transient hash is unsupported by this producer"
    defineResult state instruction (← combine (.hash (values.map (·.term)))
      (Field.modulus - 1) values)
  | "impact" =>
    let guardText ← stringField instruction "guard"
    let guard ← nativeOperand state guardText
    requireBoolean guard
    let values ← nativeArguments state instruction "inputs"
    let some group := expected.groups[state.groupCount]? | throw "unexpected native activity group"
    let expectedGuard ← if expected.groupGuards.isEmpty then pure (.constant 1) else
      match expected.groupGuards[state.groupCount]? with
      | some guard => pure guard
      | none => throw "source activity guard schedule is incomplete"
    ensure (guard.term == expectedGuard)
      "native Impact guard differs from the source-derived activity guard"
    let actualTerms := values.map (·.term)
    ensure (actualTerms == group) "native transcript activity grouping/payload mismatch"
    pure {state with groupCount := state.groupCount + 1}
  | "output" =>
    let values ← nativeArguments state instruction "vals"
    ensure (values.map (·.term) == expected.returns) "native return signature/value mismatch"
    pure state
  | _ => throw "registered native descriptor has no executable validation rule"

def opcode (instruction : Json) : String :=
  (stringField instruction "op").toOption.getD ""

def finalOutputShape (instructions : List Json) : Bool :=
  !instructions.isEmpty && (instructions.map opcode).count "output" == 1 &&
    (instructions.getLast?.map opcode).getD "" == "output"

def requireFinalOutput (instructions : List Json) : Except String Unit :=
  ensure (finalOutputShape instructions) "native program requires exactly one final Output"

def sourceMaximum : Ty → Nat
  | .native => Field.modulus - 1
  | .bool => 1
  | .uint maximum => maximum
  | .bytes _ => 0

def checkBound (state : State) (term : Term) (maximum : Nat) : Except String Unit := do
  let bounded := match term with
    | .constant value => value ≤ maximum
    | _ => state.definitions.any fun (_, fact) => fact.term == term && fact.maximum ≤ maximum
  ensure bounded "typed source range/Boolean requirement is absent from native constraints"

/-- Validate a generated Native-scalar program against an independently derived
typed statement/schedule. This does not authenticate a raw caller's Expected. -/
def validate (expected : Expected) (program : Json) : Except String Unit := do
  ensure (expected.groupGuards.isEmpty || expected.groupGuards.length == expected.groups.length)
    "source activity guard schedule length mismatch"
  fields program ["version", "inputs", "outputs", "do_communications_commitment", "instructions"]
  let version ← program.getObjVal? "version"
  fields version ["major", "minor"]
  ensure ((← natField version "major") == 3 && (← natField version "minor") == 2)
    "unsupported native producer IR version"
  ensure ((← arrayField program "inputs").isEmpty) "native root input declarations are unsupported"
  let returns ← arrayField program "outputs"
  ensure (returns.size == expected.returns.length) "native output header count mismatch"
  for output in returns do nativeType output
  ensure ((← (← program.getObjVal? "do_communications_commitment").getBool?) ==
    (expected.mode == .ledgerCall)) "native communication commitment policy mismatch"
  let instructions ← arrayField program "instructions"
  ensure (instructions.size ≤ maxInstructions && expected.inputs.length ≤ 512 &&
    expected.returns.length ≤ 256 && expected.groups.length ≤ maxInstructions &&
    expected.assertions.length ≤ maxInstructions)
    "native producer resource limit exceeded"
  requireFinalOutput instructions.toList
  let mut state : State := {}
  for (instruction, index) in instructions.toList.zipIdx do
    match validateInstruction expected state instruction with
    | .ok next => state := next
    | .error message => throw s!"native instruction {index}: {message}"
  ensure (state.inputCount == expected.inputs.length) "missing native transcript input"
  ensure (state.groupCount == expected.groups.length) "missing native transcript activity group"
  ensure (state.assertionCount == expected.assertions.length) "missing or reordered typed source assertion"
  for input in expected.inputs do
    ensure (!input.ty.isBytes) "Bytes32 must be expanded into UInt8 native inputs"
    checkBound state (.input input.identifier) (sourceMaximum input.ty)
  for (term, maximum) in expected.bounds do checkBound state term maximum

theorem final_output_required (instructions : List Json) :
    requireFinalOutput instructions = .ok () ↔ finalOutputShape instructions = true := by
  simp [requireFinalOutput, ensure]
  cases finalOutputShape instructions <;> simp
  rfl

theorem established_boolean_range (fact : Fact) (value : Nat)
    (hmax : fact.maximum ≤ 1) (hvalue : value ≤ fact.maximum) : value = 0 ∨ value = 1 := by omega

theorem require_boolean_iff (fact : Fact) :
    requireBoolean fact = .ok () ↔ fact.maximum ≤ 1 := by
  simp [requireBoolean, ensure]
  split <;> simp_all
  rfl

end Nightlean.Backend.Native
