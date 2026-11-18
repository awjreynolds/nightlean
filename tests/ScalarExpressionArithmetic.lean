import Noctium.Verification.ScalarExpressionArithmetic

namespace ScalarExpressionArithmeticTests

open Noctium Noctium.Backend Noctium.Verification
open ScalarLowering ScalarExpressionArithmetic

private def repeated : Expr .native :=
  .add (.mul (.native 3) (.native 4)) (.mul (.native 3) (.native 4))

example : ExprComplete repeated :=
  complete_add _ _
    (complete_mul _ _ (complete_native 3) (complete_native 4))
    (complete_mul _ _ (complete_native 3) (complete_native 4))

private def narrowed : Expr (.uint 15) :=
  .cast (.uint 15) (.usub (.uint 31 21) (.uint 7 6))

example : ExprComplete narrowed :=
  complete_cast _ _ (complete_usub _ _ (complete_uint 31 21) (complete_uint 7 6))

example : ExprComplete (.cast .bool repeated) :=
  complete_cast _ _ (complete_add _ _
    (complete_mul _ _ (complete_native 3) (complete_native 4))
    (complete_mul _ _ (complete_native 3) (complete_native 4)))

example : ExprComplete (.uadd (.uint 7 2) (.umul (.uint 3 2) (.uint 4 3))) :=
  complete_uadd _ _ (complete_uint 7 2)
    (complete_umul _ _ (complete_uint 3 2) (complete_uint 4 3))

example (ty : Ty) (name : String) : ExprComplete (.ref (ty := ty) name) := complete_ref ty name

private def context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
}

example : repeated.eval context [] = .ok 24 := by rfl
example : narrowed.eval context [] = .ok 15 := by rfl
example : (Expr.usub (.uint 7 2) (.uint 7 3)).eval context [] =
    .error "unsigned subtraction underflow" := by rfl
example : (Expr.cast (.uint 14) narrowed).eval context [] =
    .error "scalar conversion exceeds unsigned bound" := by rfl

private def repeatedCircuit : Circuit := {
  name := "arithmetic_cache"
  inputs := []
  constraints := []
  outputs := [{name := "result", ty := .native, value := repeated}]
}

#guard match Zkir.lowerCircuit repeatedCircuit with
  | .error _ => false
  | .ok json => match NativeRelationJson.decode json with
    | .error _ => false
    | .ok program =>
      (program.instructions.filter fun instruction => match instruction with
        | .mul .. => true
        | _ => false).length == 1

#print axioms Noctium.Verification.ScalarExpressionArithmetic.complete_native
#print axioms Noctium.Verification.ScalarExpressionArithmetic.complete_bool
#print axioms Noctium.Verification.ScalarExpressionArithmetic.complete_uint
#print axioms Noctium.Verification.ScalarExpressionArithmetic.complete_ref
#print axioms Noctium.Verification.ScalarExpressionArithmetic.complete_add
#print axioms Noctium.Verification.ScalarExpressionArithmetic.complete_mul
#print axioms Noctium.Verification.ScalarExpressionArithmetic.complete_sub
#print axioms Noctium.Verification.ScalarExpressionArithmetic.complete_uadd
#print axioms Noctium.Verification.ScalarExpressionArithmetic.complete_usub
#print axioms Noctium.Verification.ScalarExpressionArithmetic.complete_umul
#print axioms Noctium.Verification.ScalarExpressionArithmetic.complete_cast
#print axioms Noctium.Verification.ScalarExpressionArithmetic.select_step

end ScalarExpressionArithmeticTests
