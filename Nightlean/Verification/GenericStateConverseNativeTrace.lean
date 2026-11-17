import Nightlean.Verification.GenericStateConverseEffectFold
import Nightlean.Verification.GenericStateConverseSource
import Nightlean.Verification.GenericStateConverseCandidates

namespace Nightlean.Verification.GenericStateConverseNativeTrace
open Backend NativeRelation ScalarNormalization NativeState

/-- From one successful original call, construct the exact production
effect-segment evaluation and checked native trace. The witness extends only
read inputs and the final root encodes the original successor. -/
theorem source_call_native_trace (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (ctx : EvalContext) (values outputs : EvalEnv)
    (inputs : Assignment) (initial next : LedgerState)
    (slots : List Slot) (initialReads : List Cell)
    (admittedInputs : CanonicalInputs entry.circuit values inputs)
    (admittedState : GenericStateEncoding.AdmittedState state initial slots)
    (accepted : Impact.lower state entry = .ok plan)
    (modulus : ctx.modulus = Field.modulus)
    (success : entry.run ctx values initial = .ok (outputs, next)) :
    ∃ finalEnv entries witness segments finalSlots finalReads,
      entry.circuit.run ctx values = .ok outputs ∧
      GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
        ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
        (outputs ++ values, initial) = .ok (entries, (finalEnv, next)) ∧
      witness = GenericStateReadAssignment.assign inputs entries ∧
      (∀ input ∈ entry.circuit.inputs,
        witness ("%input_" ++ input.name) = inputs ("%input_" ++ input.name)) ∧
      entries.map Prod.fst = plan.reads.drop
        ((entry.circuit.inputs.filter (·.visibility == .«public»)).length) ∧
      (∀ pair ∈ entries, pair.2.val ≤ Native.sourceMaximum pair.1.ty) ∧
      GenericStateAdmission.EvaluatedChunks state ctx
        ((outputs ++ values) ++ GenericStateInputValues.decodeReads
          (plan.reads.drop
            ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
          witness) entry.effects segments ∧
      GenericStateVM.RunsChunks segments ⟨[.vector slots], initialReads⟩
        ⟨[.vector finalSlots], finalReads⟩ ∧
      GenericStateEncoding.encodeState state next = some finalSlots ∧
      (∀ guard ∈ plan.guards,
        guard.eval ctx
          ((outputs ++ values) ++ GenericStateInputValues.decodeReads
            (plan.reads.drop
              ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
            witness) = .ok true) := by
  obtain ⟨finalEnv, entries, circuit, instrumented, names,
    bounded, distinctEntries, unchanged⟩ :=
    GenericStateConverseSource.source_assignment_of_entry_run ctx state
      entry plan values outputs initial next inputs accepted modulus success
  let witness := GenericStateReadAssignment.assign inputs entries
  let reads := plan.reads.drop
    ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
  let complete := (outputs ++ values) ++
    GenericStateInputValues.decodeReads reads witness
  have candidate : ∀ read value, (read, value) ∈ entries →
      complete.lookup read.name = some (Value.pack read.ty
        (GenericStateInputValues.sourceValue read.ty value)) := by
    intro read value member
    exact GenericStateConverseCandidates.source_candidate_lookup state entry
      plan ctx values outputs initial next finalEnv entries inputs
      admittedInputs accepted circuit instrumented read value member
  obtain ⟨finalTypes, validated⟩ :=
    GenericStateEffectValidation.lower_validated_effects state entry plan accepted
  obtain ⟨chunks, chunksAccepted, operationShape⟩ :=
    GenericStateAdmission.lower_effect_chunks state entry plan accepted
  have aligned := GenericStateAdmission.effectChunks_aligned state entry.effects
    chunks chunksAccepted
  have agreement :=
    GenericStateConverseInitialEnvironment.source_initial_agreement ctx entry
      values outputs (GenericStateInputValues.decodeReads reads witness)
      inputs admittedInputs circuit
  obtain ⟨segments, finalSlots, finalReads, evaluated, trace, encodedFinal,
    _, guardTruth⟩ :=
    GenericStateConverseEffectFold.source_effects_native ctx state entry.effects
      (GenericStateEffectValidation.initialEffectTypeEnv entry) finalTypes
      (outputs ++ values) complete initial
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      entries (finalEnv, next) slots initialReads chunks validated aligned instrumented
      candidate agreement admittedState.encoded
      admittedState.distinctDeclarations admittedState.slotBound modulus
  refine ⟨finalEnv, entries, witness, segments, finalSlots, finalReads,
    circuit, instrumented, rfl, unchanged, names, bounded, evaluated,
    trace, encodedFinal, ?_⟩
  rw [GenericStateGuardTape.lower_guard_chunks state entry plan accepted]
  exact guardTruth

end Nightlean.Verification.GenericStateConverseNativeTrace
