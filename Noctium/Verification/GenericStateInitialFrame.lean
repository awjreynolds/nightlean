import Noctium.Verification.GenericStatePrefixEnvironment
import Noctium.Verification.GenericStateOutputEnvironment
import Noctium.Verification.GenericStateTypeOrder

namespace Noctium.Verification.GenericStateInitialFrame
open Backend NativeRelation ScalarNormalization Backend.Native
open GenericStatePrefixEnvironment

/-- The original output bindings start the source effect loop with values
agreeing on every source-validated input and output name. Later read witness
candidates are present only in the complete environment. -/
theorem accepted_initial_agreement (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (witness : Assignment)
    (streams : InputStreams) (publicGroups : List (List Scalar))
    (admitted : CanonicalInputs entry.circuit values witness)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ plan result,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      entry.circuit.run ctx values = .ok result ∧
      AgreesOnTypes
        ((Passes.pruneEntrypoint entry).circuit.inputs.map
          (fun input => (input.name, input.ty)) ++
          (Passes.pruneEntrypoint entry).circuit.outputs.map
            (fun output => (output.name, output.ty)))
        (result ++ values)
        ((result ++ values) ++ GenericStateInputValues.decodeReads
          (plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
            (·.visibility == .«public»)).length)) witness) := by
  obtain ⟨plan, frame, result, planAccepted, sourceRun,
    _, outputEnvironment⟩ :=
    GenericStateOutputEnvironment.accepted_output_environment state entry json
      relation ctx hash implementation values witness streams publicGroups
      admitted lowered decoded satisfies
  have validated := GenericStateAdmission.lower_circuit_validated state
    (Passes.pruneEntrypoint entry) plan planAccepted
  have ordered := GenericStateTypeOrder.typedEnvironment_input_output_order
    (Passes.pruneEntrypoint entry).circuit validated hash witness
    frame.1 (result ++ values)
    (by simpa only [Passes.pruneEntrypoint, Passes.pruneCircuit]
      using outputEnvironment)
  refine ⟨plan, result, planAccepted, sourceRun, ?_⟩
  exact initial_from_typed hash witness frame.1 _ (result ++ values)
    (GenericStateInputValues.decodeReads
      (plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
        (·.visibility == .«public»)).length)) witness) ordered

end Noctium.Verification.GenericStateInitialFrame
