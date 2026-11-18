import Noctium.Verification.GenericStateConverseEffectStep
import Noctium.Verification.GenericStateSourceReadInputs
import Noctium.Verification.GenericStateAdmission
import Noctium.Verification.GenericStateConverseGuardStep

namespace Noctium.Verification.GenericStateConverseEffectFold
open Backend NativeRelation ScalarNormalization NativeState
open GenericStatePrefixEnvironment

private theorem read_candidate_of_instrumented_step (ctx : EvalContext)
    (effect : Effect) (ordinal : Nat)
    (before after : SourceEffects.Frame)
    (tail : List (Impact.Read × Scalar)) (complete : EvalEnv)
    (source : SourceEffects.step ctx effect before = .ok after)
    (candidate : ∀ read value,
      (read, value) ∈ GenericStateSourceReadInputs.effectEntries
        effect ordinal after ++ tail →
      complete.lookup read.name = some (Value.pack read.ty
        (GenericStateInputValues.sourceValue read.ty value)))
    (modulus : ctx.modulus = Field.modulus) :
    ∀ name destination ty, effect = .readCell name destination ty →
      complete.lookup destination = after.1.lookup destination := by
  intro name destination ty equal
  subst effect
  rcases before with ⟨env, current⟩
  obtain ⟨value, _, canonical, frame⟩ :=
    GenericStateSourceTrace.readCell_step_value ctx env current name destination
      ty after modulus source
  subst after
  have member : (({name := destination, ty} : Impact.Read),
      scalar (number ty value)) ∈
      GenericStateSourceReadInputs.effectEntries
        (.readCell name destination ty) ordinal
          ((destination, Value.pack ty value) :: env, current) ++ tail := by
    simp [GenericStateSourceReadInputs.effectEntries, valueNumber_pack]
  have found := candidate {name := destination, ty}
    (scalar (number ty value)) member
  rw [GenericStateSourceReadInputs.sourceValue_roundtrip ty value canonical]
    at found
  simpa using found

/-- Source success, accepted effect chunks and the source-derived read tape
construct a checked native trace in exact effect order. Every intermediate
machine encodes the original source state at the corresponding prefix. -/
theorem source_effects_native (ctx : EvalContext) (state : List StateDecl)
    (effects : List Effect) (types finalTypes : TypeEnv)
    (sourceEnv complete : EvalEnv) (current : LedgerState)
    (ordinal : Nat) (entries : List (Impact.Read × Scalar))
    (sourceAfter : SourceEffects.Frame)
    (slots : List NativeState.Slot) (reads : List NativeState.Cell)
    (chunks : List (List Impact.Op))
    (validated : GenericStateEffectValidation.ValidatedEffects
      state types effects finalTypes)
    (aligned : GenericStateAdmission.AlignedChunks state effects chunks)
    (instrumented : GenericStateSourceReadInputs.sourceReadInputs ctx effects
      ordinal (sourceEnv, current) = .ok (entries, sourceAfter))
    (candidate : ∀ read value, (read, value) ∈ entries →
      complete.lookup read.name = some (Value.pack read.ty
        (GenericStateInputValues.sourceValue read.ty value)))
    (agrees : AgreesOnTypes types sourceEnv complete)
    (encoded : GenericStateEncoding.encodeState state current = some slots)
    (distinct : state.Pairwise (fun left right => left.name ≠ right.name))
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ segments finalSlots finalReads,
      GenericStateAdmission.EvaluatedChunks state ctx complete effects segments ∧
      GenericStateVM.RunsChunks segments
        ⟨[.vector slots], reads⟩
        ⟨[.vector finalSlots], finalReads⟩ ∧
      GenericStateEncoding.encodeState state sourceAfter.2 = some finalSlots ∧
      AgreesOnTypes finalTypes sourceAfter.1 complete ∧
      (∀ guard ∈ (GenericStateGuardTape.guardChunks effects ordinal).flatten,
        guard.eval ctx complete = .ok true) := by
  induction effects generalizing types sourceEnv current ordinal entries
      sourceAfter slots reads chunks finalTypes with
  | nil =>
    cases validated
    cases aligned
    simp only [GenericStateSourceReadInputs.sourceReadInputs,
      Except.ok.injEq] at instrumented
    cases instrumented
    exact ⟨[], slots, reads, .nil, .nil _, encoded, agrees, by simp
      [GenericStateGuardTape.guardChunks]⟩
  | cons effect rest ih =>
    obtain ⟨middle, tailEntries, sourceStep, tailSource, entriesShape⟩ :=
      GenericStateSourceReadInputs.sourceReadInputs_cons ctx effect rest ordinal
        (sourceEnv, current) sourceAfter entries instrumented
    obtain ⟨nextTypes, firstValidated, restValidated⟩ :=
      GenericStateEffectValidation.ValidatedEffects.uncons validated
    cases aligned with
    | cons first remaining =>
      obtain ⟨base, compiled, chunkShape⟩ := first
      have firstCandidate := read_candidate_of_instrumented_step ctx effect
        ordinal (sourceEnv, current) middle tailEntries complete sourceStep
        (by
          intro read value member
          apply candidate read value
          rw [entriesShape]
          exact member) modulus
      obtain ⟨segment, nextSlots, nextReads, evaluated, nativeRun,
        nextEncoded, nextAgreement⟩ :=
        GenericStateConverseEffectStep.source_effect_native ctx state types
          nextTypes effect sourceEnv complete current middle slots reads base
          firstValidated sourceStep agrees firstCandidate compiled encoded
          distinct stateBound modulus
      have firstGuard :=
        GenericStateConverseGuardStep.source_effect_guard_true ctx state types
          nextTypes effect sourceEnv complete current middle ordinal tailEntries
          firstValidated sourceStep agrees
          (by
            intro read value member
            apply candidate read value
            rw [entriesShape]
            exact member)
      have tailCandidate : ∀ read value, (read, value) ∈ tailEntries →
          complete.lookup read.name = some (Value.pack read.ty
            (GenericStateInputValues.sourceValue read.ty value)) := by
        intro read value member
        apply candidate read value
        rw [entriesShape]
        exact List.mem_append_right _ member
      obtain ⟨tailSegments, finalSlots, finalReads, tailEvaluated,
        tailTrace, finalEncoded, finalAgreement, tailGuards⟩ :=
        ih nextTypes finalTypes middle.1 middle.2
          (ordinal + (GenericStateSourceReadInputs.effectEntries
            effect ordinal middle).length)
          tailEntries sourceAfter nextSlots nextReads _ restValidated remaining
          tailSource tailCandidate nextAgreement nextEncoded
      refine ⟨segment :: tailSegments, finalSlots, finalReads,
        .cons base compiled evaluated tailEvaluated,
        .cons segment tailSegments ⟨[.vector slots], reads⟩
          ⟨[.vector nextSlots], nextReads⟩
          ⟨[.vector finalSlots], finalReads⟩ nativeRun tailTrace,
        finalEncoded, finalAgreement, ?_⟩
      intro guard member
      simp only [GenericStateGuardTape.guardChunks,
        List.flatten_cons, List.mem_append] at member
      rcases member with head | tail
      · exact firstGuard guard head
      · have sameOrdinal := GenericStateSourceReadInputs.effectEntries_length
          effect ordinal middle
        rw [← sameOrdinal] at tail
        exact tailGuards guard tail

end Noctium.Verification.GenericStateConverseEffectFold
