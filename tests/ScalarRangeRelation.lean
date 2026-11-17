import Nightlean.Verification.NativeRelationJson

namespace ScalarRangeRelationTests

open Lean
open Nightlean.Verification.NativeRelation
open Nightlean.Verification.NativeRelationJson

private def nativeType : Json := toJson ("Scalar<BLS12-381>" : String)

private def instruction (opcode : String) (fields : List (String × Json)) : Json :=
  Json.mkObj (("op", toJson opcode) :: fields)

private def root (instructions : List Json) : Json := Json.mkObj [
  ("version", Json.mkObj [("major", toJson (3 : Nat)), ("minor", toJson (2 : Nat))]),
  ("inputs", Json.arr #[]), ("outputs", Json.arr #[nativeType]),
  ("do_communications_commitment", toJson false), ("instructions", toJson instructions)]

private def rangeFixture : Json := root [
  instruction "constrain_bits" [("val", toJson ("%input_value" : String)), ("bits", toJson (8 : Nat))],
  instruction "less_than" [("a", toJson ("%input_value" : String)),
    ("b", toJson ("0x0a" : String)), ("bits", toJson (8 : Nat)),
    ("output", toJson ("%v0" : String))],
  instruction "output" [("vals", toJson (["%v0"] : List String))]]

#guard match Nightlean.Verification.NativeRelationJson.decode rangeFixture with
  | .ok program => match program.instructions with
    | [.bits (.reference value) 8, .lessThan (.reference left) (.immediate bound) 8 output,
       .output [.reference returned]] =>
      value == "%input_value" && left == value && bound.val == 10 &&
      output == "%v0" && returned == output &&
      (Nightlean.Verification.NativeRelationJson.encode program).compress == rangeFixture.compress
    | _ => false
  | .error _ => false

#guard match Nightlean.Verification.NativeRelationJson.decode (root [
    instruction "constrain_bits" [("val", toJson ("%v0" : String)), ("bits", toJson (0 : Nat))]]) with
  | .error _ => true
  | .ok _ => false

#guard match Nightlean.Verification.NativeRelationJson.decode (root [
    instruction "less_than" [("a", toJson ("%a" : String)), ("b", toJson ("%b" : String)),
      ("bits", toJson (Nightlean.ScalarPolicy.maxBits + 1)), ("output", toJson ("%v0" : String))]]) with
  | .error _ => true
  | .ok _ => false

example (hash : Hash) (witness : Assignment) (value : Operand) (width : Nat)
    (holds : Instruction.Holds hash witness (.bits value width)) :
    (value.read witness).val ≤ 2 ^ width - 1 :=
  range_constraint_bound hash witness value width holds

example (hash : Hash) (witness : Assignment) (a b : Operand) (width : Nat)
    (result : String)
    (holds : Instruction.Holds hash witness (.lessThan a b width result))
    (aBound : (a.read witness).val < 2 ^ width)
    (bBound : (b.read witness).val < 2 ^ width) :
    witness result = bit (decide ((a.read witness).val < (b.read witness).val)) :=
  less_than_sound hash witness a b width result holds aBound bBound

/-- Outside the documented range precondition, LessThan adds no arbitrary
behavior. The validator must establish both bounds before relying on its result. -/
example (hash : Hash) (witness : Assignment) (destination : String) :
    Instruction.Holds hash witness
      (.lessThan (.immediate (scalar 2)) (.immediate (scalar 0)) 1 destination) := by
  intro aBound
  have impossible : ¬ (scalar 2).val < 2 ^ 1 := by decide
  exact False.elim (impossible aBound)

end ScalarRangeRelationTests
