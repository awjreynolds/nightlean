import Noctium.Verification.GenericStateConverseCandidateEnvironment
import Noctium.Verification.GenericStateConverseCheckedPlan
import Noctium.Verification.GenericStateConversePublicPrefix
import Noctium.Verification.GenericStateOperationCompleteness

namespace Noctium.Verification.GenericStateConverseExpected
open Backend NativeRelation ScalarNormalization Backend.Native
open GenericStateCircuitParts

/-- Successful source execution satisfies every exact independent ledger-call
expected requirement once its constructed production schedule is evaluated.
The VM group equation retains every operation and its original order. -/
theorem expected_from_source_schedule (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (expected : Expected)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values result : EvalEnv) (inputs : Assignment)
    (initial next : LedgerState) (finalEnv : EvalEnv)
    (entries : List (Impact.Read × Scalar))
    (nativeOps : List NativeState.Op)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (expectedAccepted : expectedEntrypoint state entry = .ok expected)
    (planAccepted : Impact.lower state entry = .ok plan)
    (source : entry.circuit.run ctx values = .ok result)
    (instrumented : GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      (result ++ values, initial) = .ok (entries, (finalEnv, next)))
    (modulus : ctx.modulus = Field.modulus)
    (guardTruth : ∀ guard ∈ plan.guards,
      guard.eval ctx
        ((result ++ values) ++ GenericStateInputValues.decodeReads
          (plan.reads.drop
            ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
          (GenericStateReadAssignment.assign inputs entries)) = .ok true)
    (evaluated : GenericStateOps.evalPlan ctx
      ((result ++ values) ++ GenericStateInputValues.decodeReads
        (plan.reads.drop
          ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
        (GenericStateReadAssignment.assign inputs entries)) plan = .ok nativeOps) :
    (∀ requirement ∈ expected.bounds,
      (interpret hash (GenericStateReadAssignment.assign inputs entries)
        requirement.1).val ≤ requirement.2) ∧
    (∀ assertion ∈ expected.assertions,
      interpret hash (GenericStateReadAssignment.assign inputs entries)
        assertion = one) ∧
    expected.groups.map (fun group => group.map
      (interpret hash (GenericStateReadAssignment.assign inputs entries))) =
      nativeOps.map NativeState.Op.fields := by
  obtain ⟨samePlan, outputFrame, conditions, guards, operationFrame,
    sameAccepted, outputAccepted, conditionAccepted, guardAccepted,
    operationAccepted, _, groupsShape, _, _, assertionsShape, boundsShape⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_parts state entry expected
      expectedAccepted
  have samePlanEq : samePlan = plan := by
    rw [planAccepted] at sameAccepted
    exact (Except.ok.inj sameAccepted).symm
  subst samePlan
  let witness := GenericStateReadAssignment.assign inputs entries
  let complete := ((result ++ values) ++ GenericStateInputValues.decodeReads
    (plan.reads.drop
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)) witness)
  obtain ⟨typed, outputBounds, outputAssertions⟩ :=
    GenericStateConverseOutputEnvironment.source_output_environment state
      entry plan ctx hash implementation values result inputs
      (result ++ values, initial) (finalEnv, next) entries outputFrame admitted
      planAccepted instrumented source outputAccepted
  have candidateTyped :=
    GenericStateConverseCandidateEnvironment.source_candidate_environment state
      entry plan ctx hash implementation values result inputs initial next
      finalEnv entries outputFrame admitted planAccepted instrumented source
      modulus outputAccepted
  obtain ⟨constraintSuccess, _⟩ :=
    ScalarNormalization.circuit_run_steps ctx entry.circuit values result source
  have inputTyped :=
    GenericStateConverseInputAdmission.initial_typed_from_source_reads
      state entry plan ctx (result ++ values, initial) (finalEnv, next)
      entries values inputs hash admitted planAccepted instrumented
  have extendedAdmission :=
    GenericStateConverseInputAdmission.assign_preserves_canonical_inputs
      state entry plan ctx (result ++ values, initial) (finalEnv, next)
      entries values inputs admitted planAccepted instrumented
  have unused := GenericStateAdmission.lower_output_names_unused
    state entry plan values witness extendedAdmission planAccepted
  obtain ⟨_, _, originalAgreement, _⟩ :=
    GenericStateOutputCompleteness.normalizeOutputs_complete ctx hash
      implementation witness (initialAliases entry plan) values
      entry.circuit.outputs outputFrame result inputTyped.aliases unused
      (ScalarNormalization.circuit_run_steps ctx entry.circuit values result
        source).2 outputAccepted
  obtain ⟨conditionBounds, conditionAssertions⟩ :=
    ScalarNormalization.constraints_complete ctx hash implementation witness
      outputFrame.1 values originalAgreement
      entry.circuit.constraints conditions conditionAccepted constraintSuccess
  have guardSuccess :=
    GenericStateConverseGuardStep.runConstraints_of_true ctx complete
      plan.guards guardTruth
  obtain ⟨guardBounds, guardAssertions⟩ :=
    ScalarNormalization.constraints_complete ctx hash implementation witness
      outputFrame.1 complete candidateTyped.aliases plan.guards guards
      guardAccepted guardSuccess
  have fieldsAdmitted := GenericStateAdmission.lower_operations_admitted
    state entry plan planAccepted
  obtain ⟨groupMeaning, operationBounds, operationAssertions⟩ :=
    GenericStateOperationCompleteness.collectOperations_complete ctx hash
      implementation witness outputFrame.1 complete candidateTyped.aliases
      entry.span plan.operations nativeOps outputFrame.2.1 operationFrame
      operationAccepted outputBounds fieldsAdmitted evaluated
  constructor
  · intro requirement member
    rw [boundsShape] at member
    simp only [List.mem_append] at member
    rcases member with (op | condition) | guard
    · exact operationBounds requirement op
    · exact conditionBounds requirement condition
    · exact guardBounds requirement guard
  constructor
  · intro assertion member
    rw [assertionsShape] at member
    simp only [List.mem_append] at member
    rcases member with ((condition | output) | guard) | operation
    · exact conditionAssertions assertion condition
    · exact outputAssertions assertion output
    · exact guardAssertions assertion guard
    · exact operationAssertions assertion operation
  · rw [groupsShape]
    exact groupMeaning

end Noctium.Verification.GenericStateConverseExpected
