import Nightlean.Verification.GenericStateConverseInputAdmission
import Nightlean.Verification.GenericStateOutputCompleteness
import Nightlean.Verification.GenericStateOutputOrder

namespace Nightlean.Verification.GenericStateConverseOutputEnvironment
open Backend NativeRelation ScalarNormalization Backend.Native
open GenericStateCircuitParts

/-- Successful original circuit output evaluation, together with the actual
accepted output normalizer, constructs the typed internal output environment.
No expected assertion or bound is assumed. -/
theorem source_output_environment (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (ctx : EvalContext)
    (hash : Hash) (implementation : HashAgreement ctx hash)
    (values result : EvalEnv) (inputs : Assignment)
    (before after : SourceEffects.Frame)
    (entries : List (Impact.Read × Scalar))
    (frame : OutputFrame)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (accepted : Impact.lower state entry = .ok plan)
    (instrumented : GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      before = .ok (entries, after))
    (source : entry.circuit.run ctx values = .ok result)
    (outputsAccepted : normalizeOutputs
      (initialAliases entry plan) entry.circuit.outputs = .ok frame) :
    TypedEnvironment hash (GenericStateReadAssignment.assign inputs entries)
      frame.1 (result ++ values)
      (entry.circuit.outputs.map (fun output => (output.name, output.ty)) ++
        entry.circuit.inputs.map (fun input => (input.name, input.ty))) ∧
      (∀ requirement ∈ frame.2.1,
        (interpret hash (GenericStateReadAssignment.assign inputs entries)
          requirement.1).val ≤ requirement.2) ∧
      (∀ assertion ∈ frame.2.2,
        interpret hash (GenericStateReadAssignment.assign inputs entries)
          assertion = one) := by
  let witness := GenericStateReadAssignment.assign inputs entries
  have inputTyped :=
    GenericStateConverseInputAdmission.initial_typed_from_source_reads
      state entry plan ctx before after entries values inputs hash admitted
      accepted instrumented
  have validation := GenericStateAdmission.lower_circuit_validated
    state entry plan accepted
  have unused := GenericStateAdmission.lower_output_names_unused
    state entry plan values witness
      (GenericStateConverseInputAdmission.assign_preserves_canonical_inputs
        state entry plan ctx before after entries values inputs admitted
        accepted instrumented) accepted
  have outputRun :=
    (ScalarNormalization.circuit_run_steps ctx entry.circuit values result source).2
  obtain ⟨bounds, assertions, _, _⟩ :=
    GenericStateOutputCompleteness.normalizeOutputs_complete ctx hash
      implementation witness (initialAliases entry plan) values
      entry.circuit.outputs frame result inputTyped.aliases unused outputRun
      outputsAccepted
  obtain ⟨sameResult, sameRun, typed⟩ :=
    GenericStateOutputOrder.outputFold_source_bindings_validated ctx hash
      implementation witness entry.circuit values
      (initialAliases entry plan, [], []) frame inputTyped validation unused
      (by simpa [normalizeOutputs] using outputsAccepted) bounds assertions
  rw [outputRun] at sameRun
  cases sameRun
  exact ⟨typed, bounds, assertions⟩

end Nightlean.Verification.GenericStateConverseOutputEnvironment
