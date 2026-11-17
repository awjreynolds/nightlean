import Nightlean.Verification.ScalarExpressionSelect

namespace ScalarExpressionSelectTests
open Nightlean Nightlean.Verification ScalarLowering
open ScalarExpressionSelect ScalarExpressionArithmetic

example : ExprComplete (.select (.bool true) (.native 9) (.native 2)) :=
  exprComplete_select _ _ _ (complete_bool true) (complete_native 9) (complete_native 2)

example : ExprComplete (.select (.bool false) (.uint 3 1) (.cast (.uint 3) (.native 2))) :=
  exprComplete_select _ _ _ (complete_bool false) (complete_uint 3 1)
    (complete_cast (.uint 3) (.native 2) (complete_native 2))

private def ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .ok 0}

example : (Expr.select (.bool true) (.uint 3 1) (.cast (.uint 3) (.native 4))).eval ctx [] =
    .error "scalar conversion exceeds unsigned bound" := rfl

example : (Expr.select (.bool false) (.native 9) (.native 2)).eval ctx [] = .ok 2 := rfl

#print axioms Nightlean.Verification.ScalarExpressionSelect.exprComplete_select
end ScalarExpressionSelectTests
