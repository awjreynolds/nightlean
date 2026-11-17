import Nightlean.Verification.GenericStateLedgerWitness
import Nightlean.Verification.GenericStateConverseLedgerSatisfies
import Nightlean.Verification.GenericStateConverseWitnessFrame

namespace Nightlean.Verification.GenericStateConverseCompleteness
open Backend NativeRelation NativeState ScalarLowering ScalarNormalization

/-- A successful original source call constructs a satisfying assignment for
the actual emitted and strictly decoded ledger-call relation. Its ordered
authenticated Impact groups and checked native trace encode the source
successor exactly. No desired relation satisfaction, VM run, or successor is
assumed. Hash agreement and canonical input/state admission remain explicit. -/
theorem accepted_entrypoint_run_complete (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values outputs : EvalEnv) (inputs : NativeRelation.Assignment)
    (initial next : LedgerState) (slots : List Slot)
    (admittedInputs : CanonicalInputs entry.circuit values inputs)
    (admittedState : GenericStateEncoding.AdmittedState state initial slots)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (source : entry.run ctx values initial = .ok (outputs, next)) :
    ∃ (plan : Impact.Plan) (expected : Backend.Native.Expected)
      (finalEnv : EvalEnv) (entries : List (Impact.Read × Scalar))
      (native : List NativeState.Op)
      (sourceWitness witness : NativeRelation.Assignment)
      (finalSlots : List Slot) (finalReads : List Cell)
      (streams : InputStreams),
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      Backend.Native.expectedEntrypoint state (Passes.pruneEntrypoint entry) =
        .ok expected ∧
      Backend.Native.validate expected json = .ok () ∧
      GenericStateSourceReadInputs.sourceReadInputs ctx
        (Passes.pruneEntrypoint entry).effects
        (((Passes.pruneEntrypoint entry).circuit.inputs.filter
          (·.visibility == .«public»)).length)
        (outputs ++ values, initial) = .ok (entries, (finalEnv, next)) ∧
      sourceWitness = GenericStateReadAssignment.assign inputs entries ∧
      CircuitSatisfies hash relation streams witness
        (NativeState.groups native) ∧
      GenericStateCheckedSchedule.CheckedPlan ctx
        (Passes.pruneEntrypoint entry) plan values witness slots
        ⟨[.vector finalSlots], finalReads⟩ ∧
      GenericStateEncoding.encodeState state next = some finalSlots ∧
      CanonicalInputs (Passes.pruneEntrypoint entry).circuit values witness ∧
      (∀ name, witness ("%input_" ++ name) =
        sourceWitness ("%input_" ++ name)) := by
  obtain ⟨plan, expected, finalEnv, entries, sourceWitness, native,
    finalSlots, finalReads, witness, finalState, planAccepted,
    expectedAccepted, producerAccepted, instrumented, sourceWitnessShape,
    checked, encoded, canonical, expectedBounds, expectedAssertions,
    expectedGroups, planEval, bodyRun, meaning, frame⟩ :=
    GenericStateLedgerWitness.lowered_body_source_witness state entry json
      relation ctx hash implementation values outputs inputs initial next
      slots admittedInputs admittedState lowered decoded
      implementation.modulus source
  have bodyMeaning : LowerStateMeaning hash witness
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2 := by
    rw [bodyRun]
    exact meaning
  have relationSatisfies :=
    GenericStateConverseLedgerSatisfies.lowered_body_circuit_satisfies state
      entry json relation plan hash witness lowered planAccepted decoded
      bodyMeaning
  have inputAgreement :=
    GenericStateConverseWitnessFrame.expected_input_agreement state
      (Passes.pruneEntrypoint entry) expected sourceWitness witness
      expectedAccepted frame
  have authenticatedGroups :=
    GenericStateConverseLedgerSatisfies.lowered_body_authenticated_groups
      state entry json relation plan expected hash sourceWitness witness native
      lowered planAccepted decoded producerAccepted inputAgreement bodyMeaning
      expectedGroups
  let streams : InputStreams :=
    ⟨relation.inputValues .«public» witness,
      relation.inputValues .«private» witness⟩
  have authenticatedSatisfaction :
      CircuitSatisfies hash relation streams witness
        (NativeState.groups native) := by
    exact ⟨relationSatisfies.instructions, rfl, rfl,
      authenticatedGroups⟩
  have checkedFinal :=
    GenericStateConverseWitnessFrame.checkedPlan_input_frame ctx
      (Passes.pruneEntrypoint entry) plan values sourceWitness witness
      slots ⟨[.vector finalSlots], finalReads⟩ frame checked
  have canonicalFinal :=
    GenericStateConverseWitnessFrame.canonicalInputs_input_frame
      (Passes.pruneEntrypoint entry) values sourceWitness witness canonical frame
  exact ⟨plan, expected, finalEnv, entries, native, sourceWitness, witness,
    finalSlots, finalReads, streams, planAccepted, expectedAccepted,
    producerAccepted, instrumented, sourceWitnessShape,
    authenticatedSatisfaction, checkedFinal, encoded, canonicalFinal, frame⟩

end Nightlean.Verification.GenericStateConverseCompleteness
