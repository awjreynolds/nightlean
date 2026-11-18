import Noctium.Verification.GenericStateConverseEffectStep
import Noctium.Verification.GenericStateGuardTape

namespace Noctium.Verification.GenericStateConverseGuardStep
open Backend NativeRelation ScalarNormalization
open GenericStatePrefixEnvironment

theorem runConstraints_of_true (ctx : EvalContext) (env : EvalEnv)
    (conditions : List (Expr .bool))
    (truth : ∀ condition ∈ conditions,
      condition.eval ctx env = .ok true) :
    runConstraints ctx env conditions = .ok () := by
  induction conditions with
  | nil => rfl
  | cons condition rest ih =>
    simp only [runConstraints, truth condition (by simp)]
    exact ih (by intro item member; exact truth item (by simp [member]))

/-- The original successful source step makes its exact production guard
true under the complete candidate environment. Generated absence guards use
the source-recorded false relation input at the live read ordinal. -/
theorem source_effect_guard_true (ctx : EvalContext) (state : List StateDecl)
    (types nextTypes : TypeEnv) (effect : Effect)
    (sourceEnv complete : EvalEnv) (current : LedgerState)
    (after : SourceEffects.Frame) (ordinal : Nat)
    (tail : List (Impact.Read × NativeRelation.Scalar))
    (validated : GenericStateEffectValidation.EffectValidation
      state types effect nextTypes)
    (source : SourceEffects.step ctx effect (sourceEnv, current) = .ok after)
    (agrees : AgreesOnTypes types sourceEnv complete)
    (candidate : ∀ read value,
      (read, value) ∈ GenericStateSourceReadInputs.effectEntries
        effect ordinal after ++ tail →
      complete.lookup read.name = some (Value.pack read.ty
        (GenericStateInputValues.sourceValue read.ty value))) :
    ∀ guard ∈ GenericStateGuardTape.effectGuardChunk effect ordinal,
      guard.eval ctx complete = .ok true := by
  cases validated with
  | @readCell stateName destination ty declared fresh =>
    simp [GenericStateGuardTape.effectGuardChunk]
  | @readMap stateName destination keyTy valueTy key declared valid fresh =>
    simp [GenericStateGuardTape.effectGuardChunk]
  | @require condition valid =>
    obtain ⟨sourceTrue, _⟩ :=
      GenericStateConverseRequire.source_require_true ctx sourceEnv current
        condition after source
    have candidateTrue : condition.eval ctx complete = .ok true := by
      rw [← eval_scoped types sourceEnv complete agrees ctx
        GenericStateEffectValidation.stateEffectCaps condition valid]
      exact sourceTrue
    intro guard member
    simp only [GenericStateGuardTape.effectGuardChunk,
      List.mem_singleton] at member
    subst guard
    exact candidateTrue
  | @writeCell stateName ty value declared valid =>
    simp [GenericStateGuardTape.effectGuardChunk]
  | @writeMap stateName keyTy valueTy key value declared keyValid valueValid =>
    simp [GenericStateGuardTape.effectGuardChunk]
  | @requireAbsent stateName keyTy key valueTy declared keyValid =>
    let read : Impact.Read :=
      {name := GenericStateNativeReadNames.absenceName ordinal, ty := .bool}
    have falseCandidate : complete.lookup
        (GenericStateNativeReadNames.absenceName ordinal) =
        some (Value.pack .bool false) := by
      have member : (read, NativeRelation.zero) ∈
          GenericStateSourceReadInputs.effectEntries
            (.requireAbsent stateName keyTy key) ordinal after ++ tail := by
        simp [read, GenericStateSourceReadInputs.effectEntries]
      have found := candidate read NativeRelation.zero member
      simpa [read, GenericStateInputValues.sourceValue, NativeRelation.zero] using found
    intro guard member
    simp only [GenericStateGuardTape.effectGuardChunk,
      List.mem_singleton] at member
    subst guard
    simp [Expr.eval, falseCandidate, canonical_eq]
    rfl

end Noctium.Verification.GenericStateConverseGuardStep
