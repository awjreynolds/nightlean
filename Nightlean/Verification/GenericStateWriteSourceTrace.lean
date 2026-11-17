import Nightlean.Verification.GenericStateSourceTrace

namespace Nightlean.Verification.GenericStateWriteSourceTrace
open ScalarNormalization

/-- Original source cell-write success exposes both the prior typed cell and
the canonical evaluated value used in the exact source update. -/
theorem writeCell_step_value (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (name : String) (ty : Ty) (expression : Expr ty)
    (after : SourceEffects.Frame) (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.writeCell name ty expression)
      (env, state) = .ok after) :
    ∃ oldValue value : ty.Denote,
      state.cells.lookup name = some (Value.pack ty oldValue) ∧
      expression.eval ctx env = .ok value ∧ Canonical ty value ∧
      after = (env, {state with cells := SourceEffects.updateEntry name (Value.pack ty value) state.cells}) := by
  cases found : state.cells.lookup name with
  | none =>
    simp [SourceEffects.step, found, throw, throwThe, bind, Except.bind] at success
  | some raw =>
    cases typed : raw.as ty with
    | none =>
      simp [SourceEffects.step, found, typed, throw, throwThe, bind, Except.bind] at success
    | some oldValue =>
      cases evaluated : expression.eval ctx env with
      | error message =>
        simp [SourceEffects.step, found, typed, evaluated, bind, Except.bind] at success
      | ok value =>
        have rawTyped : raw = Value.pack ty oldValue := by
          cases raw <;> cases ty <;> simp_all [Value.as, Value.pack]
        subst raw
        have exactStep : SourceEffects.step ctx (.writeCell name ty expression)
            (env, state) = .ok (env, {state with cells := SourceEffects.updateEntry name (Value.pack ty value) state.cells}) := by
          simp [SourceEffects.step, found, typed, evaluated,
            bind, Except.bind, pure, Except.pure]
        rw [exactStep] at success
        exact ⟨oldValue, value, rfl, rfl,
          GenericStateEvaluationCanonical.expression_eval_canonical ctx env expression value modulus evaluated,
          (Except.ok.inj success).symm⟩

private def checkMapTypes (name : String) (keyTy valueTy : Ty)
    (entries : List (Value × Value)) : Except String PUnit :=
  forIn entries PUnit.unit fun entry _ =>
    if (entry.1.as keyTy).isNone || (entry.2.as valueTy).isNone then do
      throw s!"state map type mismatch '{name}'"
      pure (.yield PUnit.unit)
    else pure (.yield PUnit.unit)

/-- Original source map-write success exposes its canonical key/value and
exact tentative map replacement. Existing-entry validation stays on the
original evaluator path rather than becoming a new assumed condition. -/
theorem writeMap_step_values (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (name : String) (keyTy valueTy : Ty)
    (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (after : SourceEffects.Frame) (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.writeMap name keyTy valueTy keyExpr valueExpr)
      (env, state) = .ok after) :
    ∃ key : keyTy.Denote, ∃ value : valueTy.Denote, ∃ entries,
      keyExpr.eval ctx env = .ok key ∧ valueExpr.eval ctx env = .ok value ∧
      Canonical keyTy key ∧ Canonical valueTy value ∧
      state.maps.lookup name = some entries ∧
      after = (env, {state with maps := SourceEffects.updateEntry name (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries) state.maps}) := by
  cases keyEval : keyExpr.eval ctx env with
  | error message => simp [SourceEffects.step, keyEval, bind, Except.bind] at success
  | ok key =>
    cases valueEval : valueExpr.eval ctx env with
    | error message => simp [SourceEffects.step, keyEval, valueEval, bind, Except.bind] at success
    | ok value =>
      cases found : state.maps.lookup name with
      | none =>
        simp [SourceEffects.step, keyEval, valueEval, found,
          bind, Except.bind, throw, throwThe] at success
      | some entries =>
        simp only [SourceEffects.step, keyEval, valueEval, found, bind, Except.bind] at success
        change (do
          let _ ← checkMapTypes name keyTy valueTy entries
          pure (env, {state with maps := SourceEffects.updateEntry name (SourceEffects.updateEntry (Value.pack keyTy key) (Value.pack valueTy value) entries) state.maps})) =
          .ok after at success
        cases checked : checkMapTypes name keyTy valueTy entries with
        | error message =>
          rw [checked] at success
          cases success
        | ok unitResult =>
          rw [checked] at success
          change Except.ok _ = .ok after at success
          exact ⟨key, value, entries, rfl, rfl,
            GenericStateEvaluationCanonical.expression_eval_canonical ctx env keyExpr key modulus keyEval,
            GenericStateEvaluationCanonical.expression_eval_canonical ctx env valueExpr value modulus valueEval,
            rfl, (Except.ok.inj success).symm⟩

end Nightlean.Verification.GenericStateWriteSourceTrace
