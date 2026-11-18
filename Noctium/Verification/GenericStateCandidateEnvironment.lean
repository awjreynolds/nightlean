import Noctium.Verification.GenericStateOutputEnvironment
import Noctium.Verification.GenericStateReadFreshness
import Noctium.Verification.GenericStateReadAdmission
import Noctium.Verification.GenericStateReadAliasLookup
import Noctium.Verification.GenericStateTypeOrder

namespace Noctium.Verification.GenericStateCandidateEnvironment
open Backend NativeRelation ScalarNormalization Backend.Native
open GenericStateInputValues GenericStateReadEnvironment
open GenericStateCircuitParts

/-- An arbitrary satisfying relation supplies a typed environment containing
the original computed output bindings and every candidate ledger read. The
checked native tape still has to authenticate those candidates. -/
theorem accepted_candidate_environment (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (witness : Assignment)
    (streams : InputStreams) (publicGroups : List (List Scalar))
    (admitted : CanonicalInputs entry.circuit values witness)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ plan frame result,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      entry.circuit.run ctx values = .ok result ∧
      normalizeOutputs
        (GenericStateCircuitParts.initialAliases (Passes.pruneEntrypoint entry) plan)
        (Passes.pruneEntrypoint entry).circuit.outputs = .ok frame ∧
      TypedEnvironment hash witness frame.1
        ((result ++ values) ++ decodeReads
          (plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
            (·.visibility == .«public»)).length)) witness)
        (GenericStateAdmission.planTypes plan (Passes.pruneEntrypoint entry)) := by
  obtain ⟨plan, frame, result, planAccepted, sourceRun,
    normalized, sourceEnvironment⟩ :=
    GenericStateOutputEnvironment.accepted_output_environment state entry json
      relation ctx hash implementation values witness streams publicGroups
      admitted lowered decoded satisfies
  let ep := Passes.pruneEntrypoint entry
  have prunedAdmission : CanonicalInputs ep.circuit values witness :=
    ⟨admitted.unique, admitted.declared, admitted.complete, admitted.binding⟩
  have prunedRun : ep.circuit.run ctx values = .ok result := by
    simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit_run] using sourceRun
  have sourceFresh := GenericStateReadFreshness.lower_read_base_fresh
    state ep plan ctx values result witness prunedAdmission planAccepted prunedRun
  have distinct := GenericStateReadFreshness.lower_read_pairwise
    state ep plan planAccepted
  have aliases := GenericStateReadAliasLookup.normalized_read_alias_lookup
    state ep plan frame planAccepted normalized
  have candidates := GenericStateReadAdmission.accepted_read_candidates
    state entry json relation hash witness streams publicGroups
    lowered decoded satisfies
  obtain ⟨candidatePlan, candidateAccepted, typedBounded⟩ := candidates
  have samePlan : candidatePlan = plan := by
    rw [planAccepted] at candidateAccepted
    exact (Except.ok.inj candidateAccepted).symm
  subst candidatePlan
  have circuitValid := GenericStateAdmission.lower_circuit_validated
    state ep plan planAccepted
  have orderedEnvironment :=
    GenericStateTypeOrder.typedEnvironment_input_output_order ep.circuit
      circuitValid hash witness frame.1 (result ++ values)
      (by simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit]
        using sourceEnvironment)
  have extended := appendDecodedReads_existing
    (plan.reads.drop ((ep.circuit.inputs.filter
      (·.visibility == .«public»)).length))
    hash witness frame.1 (result ++ values)
    (ep.circuit.inputs.map (fun input => (input.name, input.ty)) ++
      ep.circuit.outputs.map (fun output => (output.name, output.ty)))
    orderedEnvironment
    (fun read member => by
      have fresh := sourceFresh read member
      refine ⟨fresh.1, ?_⟩
      rw [← GenericStateTypeOrder.validated_input_output_type_order
        ep.circuit circuitValid read.name]
      exact fresh.2)
    distinct aliases
    (fun read member => (typedBounded read member).1)
    (fun read member => (typedBounded read member).2)
  refine ⟨plan, frame, result, planAccepted, sourceRun, normalized, ?_⟩
  simpa only [ep, GenericStateAdmission.planTypes, readTypes,
    List.append_assoc] using extended

end Noctium.Verification.GenericStateCandidateEnvironment
