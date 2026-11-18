import Noctium.Verification.GenericStateConverseSource
import Noctium.Verification.GenericStateCircuitParts

namespace Noctium.Verification.GenericStateConverseInputBounds
open Backend NativeRelation ScalarNormalization Backend.Native

/-- Every declared native input, including source-generated ledger reads,
meets the independent producer's numeric source bound before SSA construction.
This converse fact uses source canonicality, not relation satisfaction. -/
theorem source_expected_input_bounds (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan) (expected : Expected)
    (ctx : EvalContext) (values result : EvalEnv)
    (inputs : Assignment) (initial next : LedgerState)
    (finalEnv : EvalEnv) (entries : List (Impact.Read × Scalar))
    (admitted : CanonicalInputs entry.circuit values inputs)
    (accepted : Impact.lower state entry = .ok plan)
    (expectedAccepted : expectedEntrypoint state entry = .ok expected)
    (instrumented : GenericStateSourceReadInputs.sourceReadInputs ctx entry.effects
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
      (result ++ values, initial) = .ok (entries, (finalEnv, next)))
    (modulus : ctx.modulus = Field.modulus) :
    ∀ requirement ∈ expected.inputs,
      (GenericStateReadAssignment.assign inputs entries
        requirement.identifier).val ≤ Native.sourceMaximum requirement.ty := by
  obtain ⟨samePlan, outputFrame, conditions, guards, operationFrame,
    lowered, outputs, conditionsAccepted, guardsAccepted,
    operations, inputShape, groupsShape, returns, mode,
    assertions, bounds⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_parts state entry expected
      expectedAccepted
  have planEqual : samePlan = plan := by
    rw [accepted] at lowered
    exact (Except.ok.inj lowered).symm
  subst samePlan
  have readNames := GenericStateSourceReadInputs.sourceReadInputs_names ctx
    entry.effects
    ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
    (result ++ values, initial) (finalEnv, next) entries instrumented
  rw [← GenericStateReadTape.lower_read_chunks state entry plan accepted]
    at readNames
  have readBound := GenericStateSourceReadInputs.sourceReadInputs_bounds ctx
    entry.effects
    ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)
    (result ++ values, initial) (finalEnv, next) entries modulus instrumented
  have distinct := GenericStateReadAssignment.sourceReadInputs_distinct
    state entry plan ctx (result ++ values, initial) (finalEnv, next)
    entries accepted instrumented
  intro requirement member
  rw [inputShape, GenericStateCircuitParts.inputRequirements] at member
  rcases List.mem_append.mp member with sourceInput | stateRead
  · obtain ⟨input, inputMember, same⟩ := List.mem_map.mp sourceInput
    subst requirement
    obtain ⟨value, found, canonical⟩ := admitted.complete input inputMember
    rw [GenericStateReadAssignment.assign_circuit_input state entry plan ctx
      (result ++ values, initial) (finalEnv, next) entries inputs input
      inputMember accepted instrumented]
    rw [admitted.binding input inputMember value found]
    exact GenericStateSourceReadInputs.canonical_source_bound input.ty value
      canonical
  · obtain ⟨read, readMember, same⟩ := List.mem_map.mp stateRead
    subst requirement
    have pairMember : read ∈ entries.map Prod.fst := by
      rw [readNames]
      exact readMember
    obtain ⟨pair, pairPresent, pairEqual⟩ := List.mem_map.mp pairMember
    rcases pair with ⟨found, value⟩
    simp only at pairEqual
    subst found
    have assignment := GenericStateReadAssignment.assign_member inputs entries
      distinct read value pairPresent
    simp only [GenericStateReadAssignment.identifier] at assignment
    rw [assignment]
    exact readBound (read, value) pairPresent

end Noctium.Verification.GenericStateConverseInputBounds
