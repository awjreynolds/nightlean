import Noctium.Verification.GenericStateCircuitParts
import Noctium.Verification.ScalarAdmission

namespace Noctium.Verification.GenericStateLedgerIdentifiers
open Backend NativeRelationJson

/-- The mandatory producer gate and strict decoder admit every emitted input
identifier, including the state-read suffix. The claim concerns actual names
in the accepted plan, not arbitrary strings. -/
theorem accepted_input_identifiers (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (expected : Native.Expected) (json : Lean.Json)
    (relation : NativeRelation.Program)
    (planAccepted : Impact.lower state entry = .ok plan)
    (expectedAccepted : Native.expectedEntrypoint state entry = .ok expected)
    (validated : Native.validate expected json = .ok ())
    (decoded : NativeRelationJson.decode json = .ok relation) :
    (∀ input ∈ entry.circuit.inputs,
      validIdentifier ("%input_" ++ input.name) = true) ∧
    (∀ read ∈ plan.reads.drop
      ((entry.circuit.inputs.filter (·.visibility == .«public»)).length),
      validIdentifier ("%input_" ++ read.name) = true) := by
  obtain ⟨samePlan, _, _, _, _, lowered, _, _, _, _, inputShape,
    _, _, _, _, _⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_parts state entry expected
      expectedAccepted
  have planEq : samePlan = plan := by
    rw [planAccepted] at lowered
    exact (Except.ok.inj lowered).symm
  subst samePlan
  have admitted := ScalarAdmission.input_identifiers validated decoded
  rw [inputShape, GenericStateCircuitParts.inputRequirements] at admitted
  constructor
  · intro input member
    have found := admitted
      ({identifier := "%input_" ++ input.name,
        visibility := input.visibility, ty := input.ty} : Native.InputRequirement)
    apply found
    exact List.mem_append_left _ (List.mem_map.mpr ⟨input, member, rfl⟩)
  · intro read member
    have found := admitted
      ({identifier := "%input_" ++ read.name,
        visibility := .«public», ty := read.ty} : Native.InputRequirement)
    apply found
    exact List.mem_append_right _ (List.mem_map.mpr ⟨read, member, rfl⟩)

end Noctium.Verification.GenericStateLedgerIdentifiers
