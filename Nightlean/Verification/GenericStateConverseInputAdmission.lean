import Nightlean.Verification.GenericStateConverseSource
import Nightlean.Verification.GenericStateAliases

namespace Nightlean.Verification.GenericStateConverseInputAdmission
open Backend NativeRelation ScalarNormalization

/-- Source-derived state reads extend the relation assignment without
changing the canonical admission of declared circuit inputs. -/
theorem assign_preserves_canonical_inputs (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (ctx : EvalContext)
    (before after : SourceEffects.Frame)
    (entries : List (Impact.Read × Scalar))
    (values : EvalEnv) (inputs : Assignment)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (accepted : Impact.lower state entry = .ok plan)
    (instrumented : GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      before = .ok (entries, after)) :
    CanonicalInputs entry.circuit values
      (GenericStateReadAssignment.assign inputs entries) := by
  refine ⟨admitted.unique, admitted.declared, admitted.complete, ?_⟩
  intro input member value found
  rw [GenericStateReadAssignment.assign_circuit_input state entry plan ctx
    before after entries inputs input member accepted instrumented]
  exact admitted.binding input member value found

/-- The actual combined input alias list starts with a typed source input
environment under the constructed relation assignment. -/
theorem initial_typed_from_source_reads (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (ctx : EvalContext)
    (before after : SourceEffects.Frame)
    (entries : List (Impact.Read × Scalar))
    (values : EvalEnv) (inputs : Assignment) (hash : Hash)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (accepted : Impact.lower state entry = .ok plan)
    (instrumented : GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      before = .ok (entries, after)) :
    TypedEnvironment hash (GenericStateReadAssignment.assign inputs entries)
      (GenericStateCircuitParts.initialAliases entry plan) values
      (entry.circuit.inputs.map (fun input => (input.name, input.ty))) := by
  exact GenericStateAliases.initialTypedEnvironment hash
    (GenericStateReadAssignment.assign inputs entries) entry plan values
    (assign_preserves_canonical_inputs state entry plan ctx before after entries
      values inputs admitted accepted instrumented)

end Nightlean.Verification.GenericStateConverseInputAdmission
