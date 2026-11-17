import Nightlean.Verification.GenericStateConverseOutputEnvironment
import Nightlean.Verification.GenericStateReadEnvironment
import Nightlean.Verification.GenericStateReadAliasLookup
import Nightlean.Verification.GenericStateReadTypes
import Nightlean.Verification.GenericStateTypeOrder

namespace Nightlean.Verification.GenericStateConverseCandidateEnvironment
open Backend NativeRelation ScalarNormalization Backend.Native
open GenericStateCircuitParts

/-- The source-derived read assignment gives every actual production read
alias a typed canonical value, after the original computed output bindings.
Its bounds follow from source canonicality, not from desired relation success. -/
theorem source_candidate_environment (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (ctx : EvalContext)
    (hash : Hash) (implementation : HashAgreement ctx hash)
    (values result : EvalEnv) (inputs : Assignment)
    (initial next : LedgerState) (finalEnv : EvalEnv)
    (entries : List (Impact.Read × Scalar))
    (frame : OutputFrame)
    (admitted : CanonicalInputs entry.circuit values inputs)
    (accepted : Impact.lower state entry = .ok plan)
    (instrumented : GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      (result ++ values, initial) = .ok (entries, (finalEnv, next)))
    (source : entry.circuit.run ctx values = .ok result)
    (modulus : ctx.modulus = Field.modulus)
    (outputsAccepted : normalizeOutputs
      (initialAliases entry plan) entry.circuit.outputs = .ok frame) :
    TypedEnvironment hash (GenericStateReadAssignment.assign inputs entries)
      frame.1
      ((result ++ values) ++ GenericStateInputValues.decodeReads
        (plan.reads.drop
          ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
        (GenericStateReadAssignment.assign inputs entries))
      (GenericStateAdmission.planTypes plan entry) := by
  let reads := plan.reads.drop
    ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
  let witness := GenericStateReadAssignment.assign inputs entries
  obtain ⟨outputTyped, _, _⟩ :=
    GenericStateConverseOutputEnvironment.source_output_environment state
      entry plan ctx hash implementation values result inputs
      (result ++ values, initial) (finalEnv, next) entries frame admitted
      accepted instrumented source outputsAccepted
  have ordered := GenericStateTypeOrder.typedEnvironment_input_output_order
    entry.circuit
    (GenericStateAdmission.lower_circuit_validated state entry plan accepted)
    hash witness frame.1 (result ++ values) outputTyped
  have names := GenericStateSourceReadInputs.sourceReadInputs_names ctx
    entry.effects
    ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
    (result ++ values, initial) (finalEnv, next) entries instrumented
  rw [← GenericStateReadTape.lower_read_chunks state entry plan accepted] at names
  have bounds := GenericStateSourceReadInputs.sourceReadInputs_bounds ctx
    entry.effects
    ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
    (result ++ values, initial) (finalEnv, next) entries modulus instrumented
  have distinct := GenericStateReadAssignment.sourceReadInputs_distinct
    state entry plan ctx (result ++ values, initial) (finalEnv, next)
      entries accepted instrumented
  have readBounds : ∀ read ∈ reads,
      (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty := by
    intro read member
    have pairMember : read ∈ entries.map Prod.fst := by
      rw [names]
      exact member
    obtain ⟨pair, pairPresent, pairEqual⟩ := List.mem_map.mp pairMember
    rcases pair with ⟨found, value⟩
    simp only at pairEqual
    subst found
    have assignment := GenericStateReadAssignment.assign_member inputs entries
      distinct read value pairPresent
    simp only [GenericStateReadAssignment.identifier] at assignment
    dsimp only [witness]
    rw [assignment]
    exact bounds (read, value) pairPresent
  have fresh := GenericStateReadFreshness.lower_read_base_fresh state entry
    plan ctx values result inputs admitted accepted source
  have aliases := GenericStateReadAliasLookup.normalized_read_alias_lookup
    state entry plan frame accepted outputsAccepted
  have extended := GenericStateReadEnvironment.appendDecodedReads_existing reads
    hash witness frame.1 (result ++ values)
    (entry.circuit.inputs.map (fun input => (input.name, input.ty)) ++
      entry.circuit.outputs.map (fun output => (output.name, output.ty)))
    ordered (fun read member => by
      have base := fresh read member
      refine ⟨base.1, ?_⟩
      rw [← GenericStateTypeOrder.validated_input_output_type_order
        entry.circuit
        (GenericStateAdmission.lower_circuit_validated state entry plan accepted)
        read.name]
      exact base.2)
    (GenericStateReadFreshness.lower_read_pairwise state entry plan accepted)
    (fun read member => aliases read member)
    (GenericStateReadTypes.lower_read_types state entry plan accepted)
    readBounds
  simpa only [reads, GenericStateAdmission.planTypes,
    GenericStateInputValues.readTypes, List.append_assoc] using extended

end Nightlean.Verification.GenericStateConverseCandidateEnvironment
