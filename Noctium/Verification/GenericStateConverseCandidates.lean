import Noctium.Verification.GenericStateConverseSource
import Noctium.Verification.GenericStateReadFreshness
import Noctium.Verification.GenericStatePrefixEnvironment

namespace Noctium.Verification.GenericStateConverseCandidates
open Backend NativeRelation ScalarNormalization

/-- The source-generated read assignment decodes to its exact typed
candidate, in the accepted production read order. -/
theorem source_candidate_lookup (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (ctx : EvalContext)
    (values result : EvalEnv) (initial next : LedgerState)
    (finalEnv : EvalEnv) (entries : List (Impact.Read × Scalar))
    (inputs : Assignment) (admitted : CanonicalInputs entry.circuit values inputs)
    (accepted : Impact.lower state entry = .ok plan)
    (circuit : entry.circuit.run ctx values = .ok result)
    (instrumented : GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      (result ++ values, initial) = .ok (entries, (finalEnv, next)))
    (read : Impact.Read) (value : Scalar) (member : (read, value) ∈ entries) :
    ((result ++ values) ++ GenericStateInputValues.decodeReads
      (plan.reads.drop
        ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
      (GenericStateReadAssignment.assign inputs entries)).lookup read.name =
      some (Value.pack read.ty
        (GenericStateInputValues.sourceValue read.ty value)) := by
  have names := GenericStateSourceReadInputs.sourceReadInputs_names ctx
    entry.effects
    ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
    (result ++ values, initial) (finalEnv, next) entries instrumented
  rw [← GenericStateReadTape.lower_read_chunks state entry plan accepted] at names
  have readMember : read ∈ plan.reads.drop
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length) := by
    rw [← names]
    exact List.mem_map.mpr ⟨(read, value), member, rfl⟩
  have fresh := (GenericStateReadFreshness.lower_read_base_fresh
    state entry plan ctx values result inputs admitted accepted circuit
    read readMember).1
  have distinct := GenericStateReadFreshness.lower_read_pairwise state entry plan accepted
  have unique := GenericStateReadAssignment.sourceReadInputs_distinct state entry plan
    ctx (result ++ values, initial) (finalEnv, next) entries accepted instrumented
  have assigned := GenericStateReadAssignment.assign_member inputs entries unique
    read value member
  simp only [GenericStateReadAssignment.identifier] at assigned
  have lookup := GenericStatePrefixEnvironment.candidate_read_lookup
    (result ++ values)
    (plan.reads.drop
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
    (GenericStateReadAssignment.assign inputs entries) distinct read readMember fresh
  rw [assigned] at lookup
  exact lookup

/-- A typed canonical source read is recovered unchanged after relation
input decoding. This applies to a read after any earlier state writes. -/
theorem source_candidate_canonical (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (ctx : EvalContext)
    (values result : EvalEnv) (initial next : LedgerState)
    (finalEnv : EvalEnv) (entries : List (Impact.Read × Scalar))
    (inputs : Assignment) (admitted : CanonicalInputs entry.circuit values inputs)
    (accepted : Impact.lower state entry = .ok plan)
    (circuit : entry.circuit.run ctx values = .ok result)
    (instrumented : GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      (result ++ values, initial) = .ok (entries, (finalEnv, next)))
    (read : Impact.Read) (value : read.ty.Denote)
    (canonical : Canonical read.ty value)
    (member : (read, scalar (ScalarNormalization.number read.ty value)) ∈ entries) :
    ((result ++ values) ++ GenericStateInputValues.decodeReads
      (plan.reads.drop
        ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
      (GenericStateReadAssignment.assign inputs entries)).lookup read.name =
      some (Value.pack read.ty value) := by
  have found := source_candidate_lookup state entry plan ctx values result
    initial next finalEnv entries inputs admitted accepted circuit instrumented
    read (scalar (ScalarNormalization.number read.ty value)) member
  rw [GenericStateSourceReadInputs.sourceValue_roundtrip read.ty value canonical]
    at found
  exact found

end Noctium.Verification.GenericStateConverseCandidates
