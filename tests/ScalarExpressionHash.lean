import Nightlean.Verification.ScalarExpressionHash

namespace ScalarExpressionHashTests

open Nightlean Nightlean.Verification ScalarLowering
open ScalarExpressionArithmetic ScalarExpressionHash

example : ExprComplete (.poseidon2 11 (.native 5) (.native 7)) :=
  exprComplete_poseidon2 11 (.native 5) (.native 7)
    (complete_native 5) (complete_native 7)

example : ExprComplete (.poseidon2 11 (.add (.native 3) (.native 4))
    (.add (.native 3) (.native 4))) :=
  exprComplete_poseidon2 11
    (.add (.native 3) (.native 4)) (.add (.native 3) (.native 4))
    (complete_add _ _ (complete_native 3) (complete_native 4))
    (complete_add _ _ (complete_native 3) (complete_native 4))

#print axioms ScalarExpressionHash.exprComplete_poseidon2

end ScalarExpressionHashTests
