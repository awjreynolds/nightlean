import Nightlean.Verification.GenericStateReadEnvironment
import Nightlean.Verification.GenericStateReadTypes
import Nightlean.Verification.GenericStateReadBounds

namespace Nightlean.Verification.GenericStateReadAdmission
open Backend NativeRelation ScalarNormalization
open GenericStateInputValues GenericStateReadEnvironment

/-- Every candidate ledger-read input in a satisfying accepted relation has
the declared source type and its producer-enforced numeric bound. -/
theorem accepted_read_candidates (state : List StateDecl) (entry : Entrypoint)
    (json : Lean.Json) (relation : Program) (hash : Hash)
    (witness : Assignment) (streams : InputStreams)
    (publicGroups : List (List Scalar))
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      ∀ read ∈ plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
        (·.visibility == .«public»)).length),
        read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} =
          .ok () ∧
        (witness ("%input_" ++ read.name)).val ≤ Native.sourceMaximum read.ty := by
  obtain ⟨plan, accepted, bounded⟩ :=
    GenericStateReadBounds.accepted_read_bounds state entry json relation hash
      witness streams publicGroups lowered decoded satisfies
  refine ⟨plan, accepted, ?_⟩
  intro read member
  exact ⟨GenericStateReadTypes.lower_read_types state
    (Passes.pruneEntrypoint entry) plan accepted read member,
    bounded read member⟩

end Nightlean.Verification.GenericStateReadAdmission
