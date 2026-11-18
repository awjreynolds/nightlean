import Noctium.Verification.GenericStateOutputOrder
import Noctium.Verification.GenericStateLowering
import Noctium.Verification.GenericStateSoundness

namespace Noctium.Verification.GenericStateOutputEnvironment
open Backend.Native NativeRelation ScalarNormalization GenericStateCircuitParts

/-- Actual independent ledger-call output construction produces the internal
environment consumed by source state effects. All bounds and assertions come
from its accepted expected statement. -/
theorem expected_output_environment (state : List StateDecl)
    (entry : Entrypoint) (expected : Expected)
    (accepted : expectedEntrypoint state entry = .ok expected)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (witness : Assignment)
    (values : EvalEnv)
    (admitted : CanonicalInputs entry.circuit values witness)
    (bounds : ∀ requirement ∈ expected.bounds,
      (interpret hash witness requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ expected.assertions,
      interpret hash witness term = one) :
    ∃ plan outputFrame result,
      Backend.Impact.lower state entry = .ok plan ∧
      normalizeOutputs (initialAliases entry plan) entry.circuit.outputs = .ok outputFrame ∧
      entry.circuit.outputs.mapM (evalOutput ctx values) = .ok result ∧
      TypedEnvironment hash witness outputFrame.1 (result ++ values)
        (entry.circuit.outputs.map (fun output => (output.name, output.ty)) ++
          entry.circuit.inputs.map (fun input => (input.name, input.ty))) := by
  obtain ⟨plan, outputFrame, conditions, guards, operationFrame,
    lowered, outputAccepted, _, _, operationAccepted,
    _, _, _, _, assertionShape, boundShape⟩ :=
    expectedEntrypoint_parts state entry expected accepted
  have circuitValid := GenericStateAdmission.lower_circuit_validated
    state entry plan lowered
  have unused := GenericStateAdmission.lower_output_names_unused
    state entry plan values witness admitted lowered
  have initialEnvironment := GenericStateAliases.initialTypedEnvironment
    hash witness entry plan values admitted
  obtain ⟨pieces, _, _, operationBounds, _⟩ :=
    GenericStateAdmission.expected_operation_groups entry.span outputFrame.1
      plan.operations outputFrame.2.1 operationFrame.1 operationFrame.2.1
      operationFrame.2.2 operationAccepted
  have outputBounds : ∀ requirement ∈ outputFrame.2.1,
      (interpret hash witness requirement.1).val ≤ requirement.2 := by
    intro requirement member
    apply bounds requirement
    rw [boundShape, operationBounds]
    exact List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ member))
  have outputAssertions : ∀ term ∈ outputFrame.2.2,
      interpret hash witness term = one := by
    intro term member
    apply assertions term
    rw [assertionShape]
    simp [member]
  obtain ⟨result, resultEval, environment⟩ :=
    GenericStateOutputOrder.outputFold_source_bindings_validated
      ctx hash implementation witness entry.circuit values
      (initialAliases entry plan, [], []) outputFrame initialEnvironment
      circuitValid unused outputAccepted outputBounds outputAssertions
  exact ⟨plan, outputFrame, result, lowered, outputAccepted,
    resultEval, environment⟩

/-- Arbitrary satisfaction of the actual emitted and strictly decoded
relation forces the original source circuit to produce the exact internal
output environment used by the ledger effect normalizer. -/
theorem accepted_output_environment (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (witness : Assignment)
    (streams : InputStreams) (publicGroups : List (List Scalar))
    (admitted : CanonicalInputs entry.circuit values witness)
    (lowered : Backend.Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ plan outputFrame result,
      Backend.Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      entry.circuit.run ctx values = .ok result ∧
      normalizeOutputs
        (initialAliases (Passes.pruneEntrypoint entry) plan)
        (Passes.pruneEntrypoint entry).circuit.outputs = .ok outputFrame ∧
      TypedEnvironment hash witness outputFrame.1 (result ++ values)
        (entry.circuit.outputs.map (fun output => (output.name, output.ty)) ++
          entry.circuit.inputs.map (fun input => (input.name, input.ty))) := by
  obtain ⟨plan, expected, planAccepted, expectedAccepted,
    _, bounds, assertions⟩ :=
    GenericStateLowering.accepted_relation_groups_self state entry json relation
      hash witness streams publicGroups lowered decoded satisfies
  have prunedAdmission : CanonicalInputs
      (Passes.pruneEntrypoint entry).circuit values witness :=
    ⟨admitted.unique, admitted.declared, admitted.complete, admitted.binding⟩
  obtain ⟨samePlan, frame, result, samePlanAccepted, outputAccepted,
    resultEval, environment⟩ :=
    expected_output_environment state (Passes.pruneEntrypoint entry)
      expected expectedAccepted ctx hash implementation witness values
      prunedAdmission bounds assertions
  have planEqual : samePlan = plan := by
    rw [planAccepted] at samePlanAccepted
    exact (Except.ok.inj samePlanAccepted).symm
  subst samePlan
  obtain ⟨sourceResult, sourceRun, _⟩ :=
    GenericStateSoundness.accepted_circuit_run_sound state entry json relation
      ctx hash implementation values witness streams publicGroups admitted
      lowered decoded satisfies
  have sourceSteps :=
    ScalarNormalization.circuit_run_steps ctx entry.circuit values sourceResult sourceRun
  have originalOutputEval : entry.circuit.outputs.mapM (evalOutput ctx values) =
      .ok result := by
    simpa only [Passes.pruneEntrypoint, Passes.pruneCircuit] using resultEval
  have resultEqual : sourceResult = result := by
    have outputSteps := sourceSteps.2
    rw [originalOutputEval] at outputSteps
    exact (Except.ok.inj outputSteps).symm
  subst sourceResult
  refine ⟨plan, frame, result, planAccepted, sourceRun, outputAccepted, ?_⟩
  simpa only [Passes.pruneEntrypoint, Passes.pruneCircuit] using environment

end Noctium.Verification.GenericStateOutputEnvironment
