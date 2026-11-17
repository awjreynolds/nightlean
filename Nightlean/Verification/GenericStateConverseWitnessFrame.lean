import Nightlean.Verification.GenericStateCheckedSchedule
import Nightlean.Verification.GenericStateCircuitParts
import Nightlean.Verification.ScalarValidation

namespace Nightlean.Verification.GenericStateConverseWitnessFrame
open Backend NativeRelation ScalarNormalization

theorem canonicalInputs_input_frame (entry : Entrypoint)
    (values : EvalEnv) (before after : Assignment)
    (admitted : CanonicalInputs entry.circuit values before)
    (frame : ∀ name, after ("%input_" ++ name) = before ("%input_" ++ name)) :
    CanonicalInputs entry.circuit values after := by
  refine ⟨admitted.unique, admitted.declared, admitted.complete, ?_⟩
  intro input member value found
  rw [frame input.name]
  exact admitted.binding input member value found

/-- SSA temporary bindings do not alter source candidate reads when the
ledger relation's `%input_` identifiers retain their assigned field values. -/
theorem decodeReads_input_frame (reads : List Impact.Read)
    (before after : Assignment)
    (frame : ∀ name, after ("%input_" ++ name) = before ("%input_" ++ name)) :
    GenericStateInputValues.decodeReads reads after =
      GenericStateInputValues.decodeReads reads before := by
  induction reads with
  | nil => rfl
  | cons read rest ih =>
    simp only [GenericStateInputValues.decodeReads, List.map_cons]
    rw [frame read.name]
    exact congrArg (List.cons _) ih

theorem checkedPlan_input_frame (ctx : EvalContext)
    (entry : Entrypoint) (plan : Impact.Plan) (values : EvalEnv)
    (before after : Assignment) (slots : List NativeState.Slot)
    (final : NativeState.Machine)
    (frame : ∀ name, after ("%input_" ++ name) = before ("%input_" ++ name))
    (checked : GenericStateCheckedSchedule.CheckedPlan ctx entry plan values
      before slots final) :
    GenericStateCheckedSchedule.CheckedPlan ctx entry plan values
      after slots final := by
  unfold GenericStateCheckedSchedule.CheckedPlan at checked ⊢
  rw [decodeReads_input_frame _ before after frame]
  exact checked

theorem expected_input_agreement (state : List StateDecl)
    (entry : Entrypoint) (expected : Backend.Native.Expected)
    (before after : Assignment)
    (accepted : Backend.Native.expectedEntrypoint state entry = .ok expected)
    (frame : ∀ name, after ("%input_" ++ name) = before ("%input_" ++ name)) :
    ScalarValidation.InputAgreement expected before after := by
  obtain ⟨plan, outputFrame, conditions, guards, operationFrame,
    lowered, outputs, conditionsAccepted, guardsAccepted,
    operations, inputShape, groupsShape, returns, mode,
    assertions, bounds⟩ :=
    GenericStateCircuitParts.expectedEntrypoint_parts state entry expected accepted
  intro requirement member
  rw [inputShape, GenericStateCircuitParts.inputRequirements] at member
  rcases List.mem_append.mp member with circuitInput | readInput
  · obtain ⟨input, _, same⟩ := List.mem_map.mp circuitInput
    subst requirement
    exact frame input.name
  · obtain ⟨read, _, same⟩ := List.mem_map.mp readInput
    subst requirement
    exact frame read.name

end Nightlean.Verification.GenericStateConverseWitnessFrame
