import Noctium.Verification.GenericStateConverseExpected
import Noctium.Verification.GenericStateConverseNativeTrace

namespace Noctium.Verification.GenericStateConverseResult
open Backend NativeRelation ScalarNormalization NativeState Backend.Native

/-- Original source success constructs an admitted read assignment, the exact
independent expected meaning, and a checked run of the complete production
Impact plan. No relation satisfaction or desired native trace is presumed. -/
theorem source_call_expected_checked (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (expected : Expected)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values outputs : EvalEnv) (inputs : Assignment)
    (initial next : LedgerState) (slots : List Slot)
    (admittedInputs : CanonicalInputs entry.circuit values inputs)
    (admittedState : GenericStateEncoding.AdmittedState state initial slots)
    (accepted : Impact.lower state entry = .ok plan)
    (expectedAccepted : expectedEntrypoint state entry = .ok expected)
    (modulus : ctx.modulus = Field.modulus)
    (source : entry.run ctx values initial = .ok (outputs, next)) :
    ∃ finalEnv entries witness native finalSlots finalReads,
      GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
        ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
        (outputs ++ values, initial) = .ok (entries, (finalEnv, next)) ∧
      witness = GenericStateReadAssignment.assign inputs entries ∧
      GenericStateCheckedSchedule.CheckedPlan ctx entry plan values witness
        slots ⟨[.vector finalSlots], finalReads⟩ ∧
      GenericStateEncoding.encodeState state next = some finalSlots ∧
      CanonicalInputs entry.circuit values witness ∧
      (∀ requirement ∈ expected.bounds,
        (interpret hash witness requirement.1).val ≤ requirement.2) ∧
      (∀ assertion ∈ expected.assertions,
        interpret hash witness assertion = one) ∧
      expected.groups.map (fun group => group.map (interpret hash witness)) =
        NativeState.groups native ∧
      GenericStateOps.evalPlan ctx
        (GenericStateCheckedSchedule.outputCandidates ctx entry values ++
          GenericStateInputValues.decodeReads
            (plan.reads.drop
              ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
            witness) plan = .ok native := by
  obtain ⟨sourceEnv, sourceEntries, circuit, sourceTape⟩ :=
    GenericStateConverseSource.source_read_tape_of_entry_run ctx entry values
      outputs initial next source
  let sourceWitness := GenericStateReadAssignment.assign inputs sourceEntries
  let future := GenericStateInputValues.decodeReads
    (plan.reads.drop
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
    sourceWitness
  obtain ⟨publicOps, publicCells, publicEval, publicShape, publicRun⟩ :=
    GenericStateConversePublicPrefix.source_public_prefix state entry plan ctx
      values outputs future inputs [.vector slots] [] accepted admittedInputs
      circuit modulus
  obtain ⟨finalEnv, entries, witness, segments, finalSlots, finalReads,
    sameCircuit, instrumented, witnessShape, unchanged, names, bounds,
    evaluated, trace, encodedFinal, guardTruth⟩ :=
    GenericStateConverseNativeTrace.source_call_native_trace state entry plan
      ctx values outputs inputs initial next slots publicCells admittedInputs
      admittedState accepted modulus source
  have entriesEqual : entries = sourceEntries := by
    rw [sourceTape] at instrumented
    exact (congrArg Prod.fst (Except.ok.inj instrumented)).symm
  subst entries
  have witnessEqual : witness = sourceWitness := by
    exact witnessShape
  subst witness
  have outputEval :=
    (ScalarNormalization.circuit_run_steps ctx entry.circuit values outputs
      circuit).2
  have candidateValues :
      GenericStateCheckedSchedule.outputCandidates ctx entry values =
        outputs ++ values := by
    simp only [GenericStateCheckedSchedule.outputCandidates, outputEval,
      Except.toOption, Option.getD_some]
  have prefixEval : (Impact.publicInputPlan entry.circuit.inputs {}).operations.mapM
      (GenericStateOps.evalOp ctx
        (GenericStateCheckedSchedule.outputCandidates ctx entry values ++
          GenericStateInputValues.decodeReads
            (plan.reads.drop
              ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
            sourceWitness)) = .ok publicOps := by
    rw [candidateValues]
    exact publicEval
  let native := publicOps ++ segments.flatten
  have planEval : GenericStateOps.evalPlan ctx
      (GenericStateCheckedSchedule.outputCandidates ctx entry values ++
        GenericStateInputValues.decodeReads
          (plan.reads.drop
            ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
          sourceWitness) plan = .ok native := by
    exact GenericStateConverseCheckedPlan.eval_plan_of_constructed_chunks
      state entry plan ctx _ segments publicOps accepted prefixEval
        (by rw [candidateValues]; exact evaluated)
  have checked :=
    GenericStateConverseCheckedPlan.checked_of_constructed_trace state entry
      plan ctx values sourceWitness slots finalSlots publicCells finalReads
      segments publicOps accepted prefixEval
      (by rw [candidateValues]; exact evaluated) publicRun trace
  obtain ⟨expectedBounds, expectedAssertions, expectedGroups⟩ :=
    GenericStateConverseExpected.expected_from_source_schedule state entry
      plan expected ctx hash implementation values outputs inputs initial next
      finalEnv sourceEntries native admittedInputs expectedAccepted accepted
      sameCircuit instrumented modulus guardTruth
      (by rw [← candidateValues]; exact planEval)
  have canonical :=
    GenericStateConverseInputAdmission.assign_preserves_canonical_inputs
      state entry plan ctx (outputs ++ values, initial) (finalEnv, next)
      sourceEntries values inputs admittedInputs accepted instrumented
  exact ⟨finalEnv, sourceEntries, sourceWitness, native, finalSlots,
    finalReads, instrumented, rfl, checked, encodedFinal, canonical,
    expectedBounds, expectedAssertions, expectedGroups, planEval⟩

end Noctium.Verification.GenericStateConverseResult
