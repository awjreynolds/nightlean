import Noctium.Verification.SourceEffects
import Noctium.Verification.ScalarNormalization
import Noctium.Verification.GenericStateEvaluationCanonical

namespace Noctium.Verification.GenericStateSourceTrace

open ScalarNormalization

theorem canonicalValue_sound (ctx : EvalContext) (ty : Ty)
    (value : ty.Denote) (modulus : ctx.modulus = Field.modulus)
    (checked : SourceEffects.canonicalValue ctx ty value = true) :
    Canonical ty value := by
  cases ty with
  | native =>
    exact ⟨by simpa [SourceEffects.canonicalValue, modulus, number] using checked,
      trivial⟩
  | bool =>
    cases value <;> simp [Canonical, number, Field.modulus]
  | uint maximum =>
    simp only [SourceEffects.canonicalValue, Bool.and_eq_true,
      decide_eq_true_eq] at checked
    rcases checked with ⟨⟨maximumBound, valueBound⟩, fieldBound⟩
    exact ⟨by simpa [modulus, number] using fieldBound,
      maximumBound, valueBound⟩

/-- Successful original cell reads expose the typed canonical value bound
for the later relation input assignment. -/
theorem readCell_step_value (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (name destination : String) (ty : Ty)
    (after : SourceEffects.Frame) (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.readCell name destination ty)
      (env, state) = .ok after) :
    ∃ value : ty.Denote,
      state.cells.lookup name = some (Value.pack ty value) ∧
      Canonical ty value ∧
      after = ((destination, Value.pack ty value) :: env, state) := by
  cases found : state.cells.lookup name with
  | none =>
    simp only [SourceEffects.step, found] at success
    change (Except.error s!"missing state cell '{name}'" :
      Except String SourceEffects.Frame) = .ok after at success
    cases success
  | some raw =>
    cases typed : raw.as ty with
    | none =>
      simp only [SourceEffects.step, found, typed] at success
      change (Except.error s!"state cell type mismatch '{name}'" :
        Except String SourceEffects.Frame) = .ok after at success
      cases success
    | some value =>
      cases canonical : SourceEffects.canonicalValue ctx ty value with
      | false =>
        simp only [SourceEffects.step, found, typed, canonical] at success
        change (Except.error s!"noncanonical state cell '{name}'" :
          Except String SourceEffects.Frame) = .ok after at success
        cases success
      | true =>
        have rawTyped : raw = Value.pack ty value := by
          cases raw <;> cases ty <;> simp_all [Value.as, Value.pack]
        subst raw
        have stepShape : SourceEffects.step ctx (.readCell name destination ty)
            (env, state) = .ok (((destination, Value.pack ty value) :: env), state) := by
          simp [SourceEffects.step, found, typed, canonical, pure, Except.pure]
        have final : after = ((destination, Value.pack ty value) :: env, state) := by
          rw [stepShape] at success
          exact (Except.ok.inj success).symm
        exact ⟨value, rfl, canonicalValue_sound ctx ty value modulus canonical,
          final⟩

/-- An accepted source absence effect yields the key evaluation and the
current map's missing-key fact used to build its false native read. -/
theorem requireAbsent_step_key (ctx : EvalContext) (env : EvalEnv)
    (state : LedgerState) (name : String) (keyTy : Ty)
    (keyExpr : Expr keyTy) (after : SourceEffects.Frame)
    (modulus : ctx.modulus = Field.modulus)
    (success : SourceEffects.step ctx (.requireAbsent name keyTy keyExpr)
      (env, state) = .ok after) :
    ∃ key : keyTy.Denote, ∃ entries,
      keyExpr.eval ctx env = .ok key ∧
      Canonical keyTy key ∧
      state.maps.lookup name = some entries ∧
      entries.lookup (Value.pack keyTy key) = none ∧
      after = (env, state) := by
  cases keyEval : keyExpr.eval ctx env with
  | error message =>
    simp [SourceEffects.step, keyEval, bind, Except.bind] at success
  | ok key =>
    cases mapLookup : state.maps.lookup name with
    | none =>
      simp [SourceEffects.step, keyEval, mapLookup, bind, Except.bind,
        throw, throwThe] at success
    | some entries =>
      cases found : entries.lookup (Value.pack keyTy key) with
      | some raw =>
        simp [SourceEffects.step, keyEval, mapLookup, found,
          bind, Except.bind, throw, throwThe] at success
      | none =>
        have stepShape : SourceEffects.step ctx (.requireAbsent name keyTy keyExpr)
            (env, state) = .ok (env, state) := by
          simp [SourceEffects.step, keyEval, mapLookup, found,
            bind, Except.bind, pure, Except.pure]
        rw [stepShape] at success
        cases success
        exact ⟨key, entries, rfl,
          GenericStateEvaluationCanonical.expression_eval_canonical ctx env
            keyExpr key modulus keyEval,
          rfl, found, rfl⟩

/-- The successful original source evaluator exposes an ordered frame after
each effect. This trace is derived from SourceEffects.step, including reads
and tentative ledger updates, with no independent transition semantics. -/
inductive SourceTrace (ctx : EvalContext) :
    List Effect → SourceEffects.Frame → SourceEffects.Frame → Prop where
  | nil (frame : SourceEffects.Frame) : SourceTrace ctx [] frame frame
  | cons (effect : Effect) (rest : List Effect)
      (before middle after : SourceEffects.Frame)
      (first : SourceEffects.step ctx effect before = .ok middle)
      (later : SourceTrace ctx rest middle after) :
      SourceTrace ctx (effect :: rest) before after

theorem fold_ok_iff_trace (ctx : EvalContext) (effects : List Effect)
    (before after : SourceEffects.Frame) :
    SourceEffects.fold ctx effects before = .ok after ↔
      SourceTrace ctx effects before after := by
  induction effects generalizing before with
  | nil =>
    constructor
    · intro success
      simp only [SourceEffects.fold_nil] at success
      cases success
      exact .nil _
    · intro trace
      cases trace
      rfl
  | cons effect rest ih =>
    rw [SourceEffects.fold_cons]
    constructor
    · intro success
      cases first : SourceEffects.step ctx effect before with
      | error message => simp [first, Except.bind] at success
      | ok middle =>
        simp only [first, Except.bind] at success
        exact SourceTrace.cons effect rest before middle after first
          ((ih middle).mp success)
    · intro trace
      cases trace with
      | cons =>
        rename_i middle first later
        rw [first]
        exact (ih middle).mpr later

/-- Source evaluator success gives a first source step and a successful tail
at the exact intermediate frame. -/
theorem source_cons (ctx : EvalContext) (effect : Effect)
    (rest : List Effect) (before after : SourceEffects.Frame)
    (success : SourceEffects.fold ctx (effect :: rest) before = .ok after) :
    ∃ middle,
      SourceEffects.step ctx effect before = .ok middle ∧
      SourceEffects.fold ctx rest middle = .ok after := by
  rw [SourceEffects.fold_cons] at success
  cases first : SourceEffects.step ctx effect before with
  | error message => simp [first, Except.bind] at success
  | ok middle =>
    simp only [first, Except.bind] at success
    exact ⟨middle, rfl, success⟩

end Noctium.Verification.GenericStateSourceTrace
