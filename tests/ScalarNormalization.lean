import Nightlean.Verification.ScalarNormalizationSoundness
import Nightlean.Backend.Zkir

open Nightlean Nightlean.Backend.Native Nightlean.Verification.ScalarNormalization

namespace ScalarNormalizationTests

/-- The previous derived comparison supplies an independent runtime parity oracle. -/
private inductive LegacyTerm where
  | constant (value : Nat)
  | input (identifier : String)
  | unary (opcode : String) (value : LegacyTerm)
  | binary (opcode : String) (left right : LegacyTerm)
  | select (condition yes no : LegacyTerm)
  | hash (values : List LegacyTerm)
  deriving BEq

private def legacy : Term → LegacyTerm
  | .constant value => .constant value
  | .input identifier => .input identifier
  | .unary opcode value => .unary opcode (legacy value)
  | .binary opcode left right => .binary opcode (legacy left) (legacy right)
  | .select condition yes no => .select (legacy condition) (legacy yes) (legacy no)
  | .hash values => .hash (values.map legacy)

private def terms : List Term := [
  .constant 0, .constant 1, .input "a", .input "b", .unary "neg" (.constant 0),
  .unary "not" (.constant 0), .binary "add" (.input "a") (.input "b"),
  .binary "mul" (.input "a") (.input "b"), .select (.constant 1) (.input "a") (.input "b"),
  .hash [], .hash [.constant 0], .hash [.constant 0, .constant 1],
  .hash [.hash [.constant 0], .hash [.input "a", .input "b"]]]

#guard terms.all fun left => terms.all fun right =>
  (left == right) == (legacy left == legacy right)

private def ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun domain left right => .ok ((domain + left + right) % Field.modulus)}

private def shadow : Expr .native := .letE "x" (.native 2)
  (.letE "x" (.add (.ref "x") (.native 3)) (.mul (.ref "x") (.ref "x")))

private def unusedUnderflow : Expr .native :=
  .letE "discard" (.usub (.uint 7 1) (.uint 7 2)) (.native 9)

private def eagerNarrowing : Expr (.uint 3) :=
  .select (.bool true) (.uint 3 1) (.cast (.uint 3) (.native 4))

private def boolRoundTrip : Expr .native :=
  .cast .native (.cast .bool (.native 7))

private def constraintsInOrder : Expr .native :=
  .assertE (.bool false) (.letE "discard" (.usub (.uint 7 1) (.uint 7 2)) (.native 0))

#guard (shadow.eval ctx []).toOption == some 25
private def error (result : Except String α) : Option String :=
  match result with
  | .ok _ => none
  | .error message => some message

#guard error (unusedUnderflow.eval ctx []) == some "unsigned subtraction underflow"
#guard error (eagerNarrowing.eval ctx []) == some "scalar conversion exceeds unsigned bound"
#guard (boolRoundTrip.eval ctx []).toOption == some 1
#guard error (constraintsInOrder.eval ctx []) == some "helper assertion failed"
#guard ((Expr.poseidon2 2 (.native 3) (.native 4)).eval ctx []).toOption == some 9

private def circuit (name : String) (expression : Expr ty) : Circuit :=
  {name, outputs := [{name := "result", ty, value := expression}]}

#guard (Backend.Zkir.lowerCircuit (circuit "shadow" shadow)).isOk
#guard (Backend.Zkir.lowerCircuit (circuit "unusedUnderflow" unusedUnderflow)).isOk
#guard !(Backend.Zkir.lowerCircuit (circuit "eagerNarrowing" eagerNarrowing)).isOk
#guard (Backend.Zkir.lowerCircuit (circuit "boolRoundTrip" boolRoundTrip)).isOk
#guard (Backend.Zkir.lowerCircuit (circuit "hash" (.poseidon2 2 (.native 3) (.native 4)))).isOk

#print axioms Term.equal_iff
#print axioms aliasAgreement_cons
#print axioms normalize_success
#print axioms normalize_sound
#print axioms normalize_exact

end ScalarNormalizationTests
