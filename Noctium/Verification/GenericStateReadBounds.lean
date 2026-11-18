import Noctium.Verification.GenericStateLowering
import Noctium.Verification.GenericStateAdmission

namespace Noctium.Verification.GenericStateReadBounds
open Backend NativeRelation

/-- The satisfying relation's producer bounds apply to every actual ledger
read input in the accepted Impact plan, including generated absence reads. -/
theorem accepted_read_bounds (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (relation : Program) (hash : Hash)
    (witness : Assignment) (streams : InputStreams)
    (publicGroups : List (List Scalar))
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      ∀ read ∈ plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
        (·.visibility == .«public»)).length),
        (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty := by
  obtain ⟨expected, expectedAccepted, inputBounds⟩ :=
    GenericStateLowering.accepted_relation_input_bounds_self state entry json
      relation hash witness streams publicGroups lowered decoded satisfies
  obtain ⟨plan, planAccepted, inputShape⟩ :=
    GenericStateAdmission.expectedEntrypoint_inputs state
      (Passes.pruneEntrypoint entry) expected expectedAccepted
  refine ⟨plan, planAccepted, ?_⟩
  intro read member
  apply inputBounds
    ({identifier := "%input_" ++ read.name,
      visibility := .«public», ty := read.ty} : Native.InputRequirement)
  rw [inputShape]
  exact List.mem_append_right _
    (List.mem_map.mpr ⟨read, member, rfl⟩)

end Noctium.Verification.GenericStateReadBounds
