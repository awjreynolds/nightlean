import Lean
import Nightlean.Verification.NativeRelationJson

namespace NativeRelationJsonTests

open Lean
open Nightlean.Verification.NativeRelation

private def nativeType : Json := toJson ("Scalar<BLS12-381>" : String)

private def instruction (opcode : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("op", toJson opcode) :: fields)

private def input (opcode name : String) (guard : Json := Json.null)
    (ty : Json := nativeType) : Json :=
  instruction opcode [("guard", guard), ("type", ty), ("output", toJson name)]

private def root (instructions : List Json)
    (version : Json := Json.mkObj [("major", toJson (3 : Nat)), ("minor", toJson (2 : Nat))])
    (inputs : Json := Json.arr #[])
    (outputs : Json := Json.arr #[nativeType])
    (commitment : Json := toJson false) : Json :=
  Json.mkObj [
    ("version", version), ("inputs", inputs), ("outputs", outputs),
    ("do_communications_commitment", commitment), ("instructions", toJson instructions)]

private def fixture : Json := root [
  input "public_input" "%input_root",
  instruction "impact" [("guard", toJson ("0x01" : String)),
    ("inputs", toJson (["%input_root"] : List String))],
  input "private_input" "%input_direction",
  instruction "constrain_to_boolean" [("val", toJson ("%input_direction" : String))],
  instruction "transient_hash" [("inputs", toJson (["0x01", "%secret", "%campaign"] : List String)),
    ("output", toJson ("%v0" : String))],
  instruction "cond_select" [("bit", toJson ("%input_direction" : String)),
    ("a", toJson ("%sibling" : String)), ("b", toJson ("%v0" : String)),
    ("output", toJson ("%v1" : String))],
  instruction "test_eq" [("a", toJson ("%v1" : String)), ("b", toJson ("%input_root" : String)),
    ("output", toJson ("%v2" : String))],
  instruction "assert" [("cond", toJson ("%v2" : String))],
  instruction "impact" [("guard", toJson ("0x01" : String)),
    ("inputs", toJson (["%input_root", "%v1"] : List String))],
  instruction "output" [("vals", toJson (["%v1"] : List String))]]

private def fails (json : Json) : Bool :=
  match Nightlean.Verification.NativeRelationJson.decode json with
  | .error _ => true
  | .ok _ => false

private def witness (name : String) : Scalar :=
  if name == "%input_root" then scalar 7
  else if name == "%input_direction" then one
  else if name == "%v1" then scalar 9
  else zero

/-- This checks the exact fixture shape and ordered observations, without
turning the finite test into a generic encoder/decoder theorem. -/
private def fixturePreserved : Bool :=
  match Nightlean.Verification.NativeRelationJson.decode fixture with
  | .error _ => false
  | .ok program =>
    let instructionOrder := match program.instructions with
      | [.input .«public» publicName,
         .impact (.immediate publicGuard) [.reference groupInput],
         .input .«private» privateName,
         .boolean (.reference booleanInput),
         .hash [.immediate domain, .reference secret, .reference campaign] hashOutput,
         .select (.reference direction) (.reference yesValue) (.reference noValue) selectedOutput,
         .testEq (.reference testLeft) (.reference testRight) testOutput,
         .assert (.reference asserted),
         .impact (.immediate finalGuard) [.reference finalInput, .reference finalValue],
         .output [.reference outputValue]] =>
        publicName == "%input_root" && publicGuard.val == 1 && groupInput == publicName &&
        privateName == "%input_direction" && booleanInput == privateName && domain.val == 1 &&
        secret == "%secret" && campaign == "%campaign" && hashOutput == "%v0" &&
        direction == privateName && yesValue == "%sibling" && noValue == hashOutput &&
        selectedOutput == "%v1" && testLeft == selectedOutput && testRight == publicName &&
        testOutput == "%v2" && asserted == testOutput && finalGuard.val == 1 &&
        finalInput == publicName && finalValue == selectedOutput && outputValue == selectedOutput
      | _ => false
    program.outputArity == 1 && !program.communicationsCommitment && instructionOrder &&
      program.inputValues .«public» witness == [scalar 7] &&
      program.inputValues .«private» witness == [one] &&
      program.groups witness == [[scalar 7], [scalar 7, scalar 9]] &&
      program.returns witness == [scalar 9]

#guard fixturePreserved

-- A finite fixture round trip exercises the executable encoder and decoder.
-- It is not a generic round-trip theorem for arbitrary Program values.
#guard match Nightlean.Verification.NativeRelationJson.decode fixture with
  | .ok program => (Nightlean.Verification.NativeRelationJson.encode program).compress == fixture.compress
  | .error _ => false

#guard match Nightlean.Verification.NativeRelationJson.decode
    (root [] (outputs := Json.arr #[nativeType, nativeType]) (commitment := toJson true)) with
  | .ok program => program.outputArity == 2 && program.communicationsCommitment &&
      (Nightlean.Verification.NativeRelationJson.encode program).compress ==
        (root [] (outputs := Json.arr #[nativeType, nativeType]) (commitment := toJson true)).compress
  | .error _ => false

#guard fails (root [] (version := Json.mkObj [("major", toJson (3 : Nat)), ("minor", toJson (3 : Nat))]))
#guard fails (Json.mkObj [
  ("version", Json.mkObj [("major", toJson (3 : Nat)), ("minor", toJson (2 : Nat))]),
  ("inputs", Json.arr #[]), ("outputs", Json.arr #[nativeType]),
  ("do_communications_commitment", toJson false), ("instructions", Json.arr #[]), ("extra", Json.null)])
#guard fails (Json.mkObj [
  ("version", Json.mkObj [("major", toJson (3 : Nat)), ("minor", toJson (2 : Nat))]),
  ("inputs", Json.arr #[]), ("do_communications_commitment", toJson false),
  ("instructions", Json.arr #[])])
#guard fails (root [] (inputs := Json.arr #[toJson ("root" : String)]))
#guard fails (root [] (outputs := Json.arr #[toJson ("Bool" : String)]))
#guard fails (root [] (commitment := toJson ("false" : String)))

#guard fails (root [instruction "impact" [("guard", toJson ("0x00" : String)),
  ("inputs", toJson ([] : List String))]])
#guard fails (root [instruction "impact" [("guard", toJson ("%guard" : String)),
  ("inputs", toJson ([] : List String))]])
#guard fails (root [instruction "unknown_op" []])
#guard fails (root [instruction "add" [("a", toJson ("0x01" : String)),
  ("output", toJson ("%v0" : String))]])
#guard fails (root [instruction "add" [("a", toJson ("0x01" : String)),
  ("b", toJson ("0x01" : String)), ("output", toJson ("%v0" : String)), ("extra", Json.null)]])
#guard fails (root [input "public_input" "%input_root" (toJson ("0x01" : String))])
#guard fails (root [input "public_input" "%input_root" Json.null (toJson ("Bool" : String))])
#guard fails (root [instruction "impact" [("guard", toJson ("0x0000" : String)),
  ("inputs", toJson ([] : List String))]])
#guard fails (root [instruction "impact" [("guard", toJson ("0x0100" : String)),
  ("inputs", toJson ([] : List String))]])
#guard fails (root [instruction "impact" [("guard",
  toJson ("0x01000000fffffffffe5bfeff02a4bd5305d8a10908d83933487d9d2953a7ed73" : String)),
  ("inputs", toJson ([] : List String))]])
#guard fails (root [instruction "impact" [("guard", toJson ("0x0" : String)),
  ("inputs", toJson ([] : List String))]])
#guard fails (root [instruction "impact" [("guard", toJson ("0xFF" : String)),
  ("inputs", toJson ([] : List String))]])

example (hash : Hash) (assigned : Assignment) (condition : Operand)
    (holds : Instruction.Holds hash assigned (.assert condition)) :
    condition.read assigned ≠ zero := holds

example (a b result : Scalar)
    (test : result = bit (decide (a = b))) (assertion : result ≠ zero) : a = b :=
  test_eq_assert_sound a b result test assertion

example (a b : Scalar) (different : a ≠ b) (result : Scalar)
    (test : result = bit (decide (a = b))) (assertion : result ≠ zero) : False := by
  exact different (test_eq_assert_sound a b result test assertion)

#eval IO.println "NativeRelationJson decoder checks passed"

end NativeRelationJsonTests
