import Nightlean.Verification.GenericStateEffectStep

namespace Nightlean.Verification.GenericStateEffectFold
open Backend NativeState
open GenericStatePrefixEnvironment GenericStateEffectStep

/-- A checked native segment for every accepted source effect yields the
original ordered source fold and the exact encoded successor after each
segment. Fresh authenticated reads extend the source environment for all
following guards and writes. -/
theorem checked_effects_fold (ctx : EvalContext) (state : List StateDecl)
    (effects : List Effect) (types finalTypes : TypeEnv)
    (sourceEnv complete : EvalEnv) (current : LedgerState)
    (slots : List NativeState.Slot) (reads : List NativeState.Cell)
    (segments : List (List NativeState.Op)) (final : NativeState.Machine)
    (validated : GenericStateEffectValidation.ValidatedEffects
      state types effects finalTypes)
    (evaluated : GenericStateAdmission.EvaluatedChunks state ctx complete
      effects segments)
    (trace : GenericStateVM.RunsChunks segments
      ⟨[.vector slots], reads⟩ final)
    (candidates : ∀ effect ∈ effects, ReadCandidate effect complete)
    (guards : ∀ effect ∈ effects, GuardTrue ctx effect complete)
    (agrees : AgreesOnTypes types sourceEnv complete)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ finalEnv finalState finalSlots finalReads,
      SourceEffects.fold ctx effects (sourceEnv, current) =
        .ok (finalEnv, finalState) ∧
      GenericStateEncoding.encodeState state finalState = some finalSlots ∧
      final = ⟨[.vector finalSlots], finalReads⟩ ∧
      AgreesOnTypes finalTypes finalEnv complete := by
  induction effects generalizing types sourceEnv current slots reads segments
      final finalTypes with
  | nil =>
    cases validated
    cases evaluated
    cases trace
    exact ⟨sourceEnv, current, slots, reads, rfl, encoded, rfl, agrees⟩
  | cons effect rest ih =>
    obtain ⟨nextTypes, firstValidated, restValidated⟩ :=
      GenericStateEffectValidation.ValidatedEffects.uncons validated
    cases evaluated with
    | @cons _ _ operations segmentsTail base compiled firstEval restEvaluated =>
      cases trace with
      | cons =>
        rename_i middle firstRun restRun
        obtain ⟨nextEnv, nextState, nextSlots, nextReads,
          firstStep, nextEncoded, middleShape, nextAgrees⟩ :=
          checked_effect_step ctx state types nextTypes effect sourceEnv complete
            current slots reads base operations middle firstValidated agrees
            (candidates effect (by simp)) (guards effect (by simp))
            compiled firstEval firstRun encoded distinct stateBound modulus
        subst middle
        obtain ⟨finalEnv, finalState, finalSlots, finalReads,
          tailFold, tailEncoded, finalShape, finalAgrees⟩ :=
          ih nextTypes finalTypes nextEnv nextState nextSlots nextReads
            segmentsTail final restValidated restEvaluated restRun
            (fun item member => candidates item (by simp [member]))
            (fun item member => guards item (by simp [member]))
            nextAgrees nextEncoded
        refine ⟨finalEnv, finalState, finalSlots, finalReads, ?_,
          tailEncoded, finalShape, finalAgrees⟩
        rw [SourceEffects.fold_cons, firstStep]
        exact tailFold

end Nightlean.Verification.GenericStateEffectFold
