import Nightlean.Verification.ScalarLowering
import Nightlean.Verification.ScalarExpressionArithmetic
import Nightlean.Verification.ScalarExpressionControl
import Nightlean.Verification.ScalarExpressionAssertion
import Nightlean.Verification.ScalarExpressionHash
import Nightlean.Verification.ScalarExpressionSelect

namespace Nightlean.Verification.ScalarExpressionLowering

open Lean Backend NativeRelation NativeRelationJson ScalarNormalization
open ScalarLowering ScalarWitness ScalarInstructionEncoding ScalarRangeLowering

open ScalarExpressionArithmetic ScalarExpressionControl

/-- Every expression admitted by its actual source validator and successful
source evaluation extends any satisfying lowerer assignment constructively. -/
theorem lowerExpr_complete (expression : Expr ty) : ExprComplete expression := by
  induction expression with
  | native number => exact ScalarExpressionArithmetic.complete_native number
  | bool value => exact ScalarExpressionArithmetic.complete_bool value
  | uint maximum number => exact ScalarExpressionArithmetic.complete_uint maximum number
  | ref name => exact ScalarExpressionArithmetic.complete_ref _ name
  | add left right leftComplete rightComplete =>
    exact ScalarExpressionArithmetic.complete_add left right leftComplete rightComplete
  | mul left right leftComplete rightComplete =>
    exact ScalarExpressionArithmetic.complete_mul left right leftComplete rightComplete
  | sub left right leftComplete rightComplete =>
    exact ScalarExpressionArithmetic.complete_sub left right leftComplete rightComplete
  | uadd left right leftComplete rightComplete =>
    exact ScalarExpressionArithmetic.complete_uadd left right leftComplete rightComplete
  | usub left right leftComplete rightComplete =>
    exact ScalarExpressionArithmetic.complete_usub left right leftComplete rightComplete
  | umul left right leftComplete rightComplete =>
    exact ScalarExpressionArithmetic.complete_umul left right leftComplete rightComplete
  | cast target value valueComplete =>
    exact ScalarExpressionArithmetic.complete_cast target value valueComplete
  | letE name value body valueComplete bodyComplete =>
    exact ScalarExpressionControl.exprComplete_letE name value body valueComplete bodyComplete
  | assertE condition body conditionComplete bodyComplete =>
    exact ScalarExpressionAssertion.exprComplete_assertE condition body conditionComplete bodyComplete
  | disclose span value valueComplete =>
    exact ScalarExpressionControl.exprComplete_disclose span value valueComplete
  | eq left right leftComplete rightComplete =>
    exact ScalarExpressionControl.exprComplete_eq left right leftComplete rightComplete
  | select condition yes no conditionComplete yesComplete noComplete =>
    exact ScalarExpressionSelect.exprComplete_select condition yes no conditionComplete yesComplete noComplete
  | poseidon2 domain left right leftComplete rightComplete =>
    exact ScalarExpressionHash.exprComplete_poseidon2 domain left right leftComplete rightComplete

end Nightlean.Verification.ScalarExpressionLowering
