import Noctium.Verification.ScalarExpressionLowering

namespace ScalarExpressionLoweringTests

open Noctium Noctium.Verification ScalarLowering
open ScalarExpressionLowering

example : ExprComplete
    (.letE "x" (.poseidon2 11 (.native 3) (.native 4))
      (.assertE (.bool true) (.select (.bool true) (.ref "x") (.native 0)))) :=
  lowerExpr_complete _

private def ctx : EvalContext :=
  {modulus := Field.modulus, poseidon2 := fun _ _ _ => .ok 0}

example : (Expr.select (.bool true) (.native 9)
    (.assertE (.bool false) (.native 0))).eval ctx [] =
    .error "helper assertion failed" := rfl

#print axioms ScalarExpressionLowering.lowerExpr_complete

end ScalarExpressionLoweringTests
