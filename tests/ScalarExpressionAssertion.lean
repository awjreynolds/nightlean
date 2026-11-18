import Noctium.Verification.ScalarExpressionAssertion

namespace ScalarExpressionAssertionTests
open Noctium Noctium.Verification ScalarLowering
open ScalarExpressionAssertion ScalarExpressionArithmetic

example : ExprComplete (.assertE (.bool true) (.native 9)) :=
  exprComplete_assertE _ _ (complete_bool true) (complete_native 9)

example : ExprComplete (.assertE (.bool true) (.assertE (.bool true) (.uint 7 2))) :=
  exprComplete_assertE _ _ (complete_bool true)
    (exprComplete_assertE _ _ (complete_bool true) (complete_uint 7 2))

private def ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .ok 0}

example : (Expr.assertE (.bool false) (.usub (.uint 7 1) (.uint 7 2))).eval ctx [] =
    .error "helper assertion failed" := rfl

example : (Expr.assertE (.bool true) (.usub (.uint 7 1) (.uint 7 2))).eval ctx [] =
    .error "unsigned subtraction underflow" := rfl

#print axioms Noctium.Verification.ScalarExpressionAssertion.exprComplete_assertE
end ScalarExpressionAssertionTests
