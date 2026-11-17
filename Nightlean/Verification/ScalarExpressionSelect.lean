import Nightlean.Verification.ScalarExpressionArithmetic

namespace Nightlean.Verification.ScalarExpressionSelect
open Lean Backend NativeRelation NativeRelationJson ScalarNormalization ScalarLowering ScalarWitness ScalarAllocation

private def selectSuffix (condition yes no : String) : StateM Zkir.LowerState String := do
  let key : ExpressionKey := ("cond_select", [condition, yes, no], none)
  if let some existing := (← get).expressions.lookup key then return existing
  let output ← Zkir.fresh
  Zkir.emit "cond_select" [("bit", toJson condition), ("a", toJson yes), ("b", toJson no), ("output", toJson output)]
  modify fun state => {state with expressions := (key, output) :: state.expressions}
  pure output

private theorem selectSuffix_preserves (condition yes no : String) : PreservesFrame (selectSuffix condition yes no) := by
  intro state
  cases hit : state.expressions.lookup ("cond_select", [condition, yes, no], none) with
  | some output =>
    simp [selectSuffix, hit, StateT.run_bind, StateT.run_get, StateT.run_pure]
    exact Frame.refl _
  | none =>
    simp [selectSuffix, hit, Zkir.fresh, Zkir.emit, Zkir.instruction,
      StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_set, StateT.run_pure]
    constructor
    · exact Nat.le_add_right _ _
    · change state.instructions.size + (state.next + 1 - state.next) ≤ (state.instructions.push _).size
      simp

private theorem selectSuffix_run (condition yes no : String) (state : Zkir.LowerState) :
    (selectSuffix condition yes no).run state =
      match state.expressions.lookup ("cond_select", [condition, yes, no], none) with
      | some output => (output, state)
      | none => (freshName state.next, appendFreshState state
          (Zkir.instruction "cond_select" [("bit", toJson condition), ("a", toJson yes), ("b", toJson no),
            ("output", toJson (freshName state.next))])
          ("cond_select", [condition, yes, no], none) (freshName state.next)) := by
  cases hit : state.expressions.lookup ("cond_select", [condition, yes, no], none) <;>
    simp [selectSuffix, hit, Zkir.fresh, Zkir.emit, appendFreshState, freshName,
      StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_set] <;> rfl

/-- Both select arms execute before the cached native selector. The constructor
therefore preserves partial-operation requirements from either source arm. -/
theorem exprComplete_select (condition : Expr .bool) (yes no : Expr ty)
    (conditionComplete : ExprComplete condition) (yesComplete : ExprComplete yes) (noComplete : ExprComplete no) :
    ExprComplete (.select condition yes no) := by
  intro ctx hash implementation inputs witness state normalAliases values types value
    valid success aliases lowerAliases stateMeaning budget
  have validation := valid
  change (do condition.validate {poseidon2 := true} types; yes.validate {poseidon2 := true} types; no.validate {poseidon2 := true} types) = .ok () at validation
  simp only [ScalarValidation.bind_ok] at validation
  obtain ⟨conditionUnit, conditionValid, yesUnit, yesValid, noValid⟩ := validation
  have sourceSuccess := success
  cases conditionEval : condition.eval ctx values with
  | error message => simp [Expr.eval, conditionEval, Bind.bind, Except.bind] at success
  | ok conditionValue =>
    cases yesEval : yes.eval ctx values with
    | error message => simp [Expr.eval, conditionEval, yesEval, Bind.bind, Except.bind] at success
    | ok yesValue =>
      cases noEval : no.eval ctx values with
      | error message => simp [Expr.eval, conditionEval, yesEval, noEval, Bind.bind, Except.bind] at success
      | ok noValue =>
        have lastPreserves : ∀ (conditionText yesText : String), PreservesFrame (do
            let noText ← Zkir.lowerExpr no
            selectSuffix conditionText yesText noText) := by
          intro conditionText yesText
          exact bind_preserves _ _ (lowerExpr_preserves no) (selectSuffix_preserves conditionText yesText)
        have suffixPreserves : ∀ (conditionText : String), PreservesFrame (do
            let yesText ← Zkir.lowerExpr yes
            let noText ← Zkir.lowerExpr no
            selectSuffix conditionText yesText noText) := by
          intro conditionText
          exact bind_preserves _ _ (lowerExpr_preserves yes) (lastPreserves conditionText)
        have firstBudget : ((Zkir.lowerExpr condition).run state).2.next ≤ Native.maxInstructions := by
          apply bind_middle_budget (Zkir.lowerExpr condition) (fun conditionText => do
            let yesText ← Zkir.lowerExpr yes
            let noText ← Zkir.lowerExpr no
            selectSuffix conditionText yesText noText) state suffixPreserves Native.maxInstructions
          exact budget
        obtain ⟨first⟩ := conditionComplete ctx hash implementation inputs witness state normalAliases values types conditionValue
          conditionValid conditionEval aliases lowerAliases stateMeaning firstBudget
        have remainingBudget : ((do
            let yesText ← Zkir.lowerExpr yes
            let noText ← Zkir.lowerExpr no
            selectSuffix first.text yesText noText).run first.finalState).2.next ≤ Native.maxInstructions := by
          have bound := budget
          change ((do
            let conditionText ← Zkir.lowerExpr condition
            let yesText ← Zkir.lowerExpr yes
            let noText ← Zkir.lowerExpr no
            selectSuffix conditionText yesText noText).run state).2.next ≤ _ at bound
          rw [StateT.run_bind, first.run] at bound
          exact bound
        have secondBudget := bind_middle_budget (Zkir.lowerExpr yes) (fun yesText => do
          let noText ← Zkir.lowerExpr no
          selectSuffix first.text yesText noText) first.finalState (lastPreserves first.text) Native.maxInstructions remainingBudget
        obtain ⟨second⟩ := yesComplete ctx hash implementation inputs first.finalWitness first.finalState normalAliases values types yesValue
          yesValid yesEval aliases first.aliasAgreement first.stateMeaning secondBudget
        have afterYesBudget : ((do let noText ← Zkir.lowerExpr no; selectSuffix first.text second.text noText).run second.finalState).2.next ≤ Native.maxInstructions := by
          have bound := remainingBudget
          rw [StateT.run_bind, second.run] at bound
          exact bound
        have thirdBudget := bind_middle_budget (Zkir.lowerExpr no) (selectSuffix first.text second.text)
          second.finalState (selectSuffix_preserves first.text second.text) Native.maxInstructions afterYesBudget
        obtain ⟨third⟩ := noComplete ctx hash implementation inputs second.finalWitness second.finalState normalAliases values types noValue
          noValid noEval aliases second.aliasAgreement second.stateMeaning thirdBudget
        have nativeBudget : ((selectSuffix first.text second.text third.text).run third.finalState).2.next ≤ Native.maxInstructions := by
          have bound := afterYesBudget
          rw [StateT.run_bind, third.run] at bound
          exact bound
        have firstNext : state.next ≤ first.finalState.next := by
          simpa only [first.run] using lowerExpr_next condition state
        have secondNext : first.finalState.next ≤ second.finalState.next := by
          simpa only [second.run] using lowerExpr_next yes first.finalState
        have thirdNext : second.finalState.next ≤ third.finalState.next := by
          simpa only [third.run] using lowerExpr_next no second.finalState
        have conditionAfterYes := OperandMeaning.of_frame hash inputs first.finalWitness second.finalWitness
          first.finalState.next first.text first.normalized.term first.operandMeaning first.textScope second.frame
        have conditionScope := first.textScope.mono secondNext
        have conditionMeaning := OperandMeaning.of_frame hash inputs second.finalWitness third.finalWitness
          second.finalState.next first.text first.normalized.term conditionAfterYes conditionScope third.frame
        have yesMeaning := OperandMeaning.of_frame hash inputs second.finalWitness third.finalWitness
          second.finalState.next second.text second.normalized.term second.operandMeaning second.textScope third.frame
        have boolean : interpret hash inputs first.normalized.term = zero ∨ interpret hash inputs first.normalized.term = one := by
          cases conditionValue
          · exact Or.inl (by simpa [number, scalar_zero] using first.represents.2.2)
          · exact Or.inr (by simpa [number, scalar_one] using first.represents.2.2)
        obtain ⟨native⟩ := ScalarExpressionArithmetic.select_step hash inputs third.finalWitness third.finalState
          (selectSuffix first.text second.text third.text) first.text second.text third.text
          first.normalized.term second.normalized.term third.normalized.term third.stateMeaning
          conditionMeaning yesMeaning third.operandMeaning (conditionScope.mono thirdNext)
          (second.textScope.mono thirdNext) third.textScope boolean (selectSuffix_run _ _ _ _) nativeBudget
        obtain ⟨normalized, normalization, represents⟩ := normalize_success ctx hash implementation inputs normalAliases values aliases
          (.select condition yes no) value sourceSuccess
        have termEq : normalized.term = .select first.normalized.term second.normalized.term third.normalized.term := by
          have actual := normalization
          simp only [Native.normalize, first.normalization, second.normalization, third.normalization] at actual
          cases actual
          simp only [Native.requireSourceType_eq]
        refine ⟨{
          text := native.text
          finalState := native.finalState
          finalWitness := native.finalWitness
          normalized
          run := ?_
          normalization
          represents
          operandMeaning := by rw [termEq]; exact native.operandMeaning
          textScope := native.textScope
          stateMeaning := native.stateMeaning
          budget := native.budget
          aliasAgreement := ?_
          aliasesPreserved := native.aliasesPreserved.trans (third.aliasesPreserved.trans (second.aliasesPreserved.trans first.aliasesPreserved))
          frame := ?_ }⟩
        · change ((do
            let conditionText ← Zkir.lowerExpr condition
            let yesText ← Zkir.lowerExpr yes
            let noText ← Zkir.lowerExpr no
            selectSuffix conditionText yesText noText).run state) = _
          rw [StateT.run_bind, first.run]
          change ((do
            let yesText ← Zkir.lowerExpr yes
            let noText ← Zkir.lowerExpr no
            selectSuffix first.text yesText noText).run first.finalState) = _
          rw [StateT.run_bind, second.run]
          change ((do let noText ← Zkir.lowerExpr no; selectSuffix first.text second.text noText).run second.finalState) = _
          rw [StateT.run_bind, third.run]
          exact native.run
        · rw [native.aliasesPreserved]
          exact LowerAliasAgreement.of_frame hash inputs third.finalWitness native.finalWitness third.finalState.next
            normalAliases third.finalState.aliases values third.aliasAgreement third.stateMeaning.aliases native.frame
        · intro name scope
          rw [native.frame name (InScope.mono (Nat.le_trans firstNext (Nat.le_trans secondNext thirdNext)) scope)]
          rw [third.frame name (InScope.mono (Nat.le_trans firstNext secondNext) scope)]
          rw [second.frame name (InScope.mono firstNext scope)]
          exact first.frame name scope

end Nightlean.Verification.ScalarExpressionSelect
