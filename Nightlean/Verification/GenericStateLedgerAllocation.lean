import Nightlean.Verification.ScalarAdmission
import Nightlean.Verification.GenericStateLowering

namespace Nightlean.Verification.GenericStateLedgerAllocation
open Lean Backend Backend.Native NativeRelation
open ScalarAllocation

private theorem list_mapM_preserves (values : List α)
    (function : α → StateM Zkir.LowerState β)
    (preserves : ∀ value, PreservesFrame (function value)) :
    PreservesFrame (values.mapM function) := by
  induction values with
  | nil => exact pure_preserves _
  | cons value rest ih =>
    simp only [List.mapM_cons]
    apply bind_preserves _ _ (preserves value)
    intro result
    exact ih

/-- Ledger lowering preserves the emitted-instruction witness for every SSA
allocation in the actual body. Alias updates leave both frame counters alone. -/
theorem lowerEntrypointBody_preserves (entry : Entrypoint) (plan : Impact.Plan) :
    PreservesFrame (Zkir.lowerEntrypointBody entry plan) := by
  unfold Zkir.lowerEntrypointBody
  apply bind_preserves
  · apply forIn_preserves
    intro input accumulator
    apply bind_preserves _ _ (emit_preserves _ _)
    intro ignored
    apply bind_preserves _ _ (constrainType_preserves _ _)
    intro ignored
    exact pure_preserves _
  · intro ignored
    apply bind_preserves
    · apply forIn_preserves
      intro condition accumulator
      apply bind_preserves _ _ (lowerExpr_preserves _)
      intro value
      apply bind_preserves _ _ (emit_preserves _ _)
      intro ignored
      exact pure_preserves _
    · intro ignored
      apply bind_preserves
      · apply forIn_preserves
        intro output accumulator
        apply bind_preserves _ _ (lowerExpr_preserves _)
        intro value
        apply bind_preserves _ _ (modify_preserves _ (by
          intro state
          change Frame state {state with aliases := (output.name, value) :: state.aliases}
          constructor <;> simp))
        intro ignored
        exact pure_preserves _
      · intro ignored
        apply bind_preserves
        · apply forIn_preserves
          intro read accumulator
          apply bind_preserves _ _ (emit_preserves _ _)
          intro ignored
          apply bind_preserves _ _ (constrainType_preserves _ _)
          intro ignored
          exact pure_preserves _
        · intro ignored
          apply bind_preserves
          · apply forIn_preserves
            intro condition accumulator
            apply bind_preserves _ _ (lowerExpr_preserves _)
            intro value
            apply bind_preserves _ _ (emit_preserves _ _)
            intro ignored
            exact pure_preserves _
          · intro ignored
            apply bind_preserves
            · apply forIn_preserves
              intro operation accumulator
              apply bind_preserves _ _ (list_mapM_preserves operation.fields
                Zkir.lowerExpr (fun expression => lowerExpr_preserves expression))
              intro values
              apply bind_preserves _ _ (bindPublic_preserves values)
              intro ignored
              exact pure_preserves _
            · intro ignored
              exact emit_preserves _ _

/-- Starting from the empty state, each allocated name has an instruction in
the body result. -/
theorem lowerEntrypointBody_allocated (entry : Entrypoint) (plan : Impact.Plan) :
    ((Zkir.lowerEntrypointBody entry plan).run {}).2.next ≤
      ((Zkir.lowerEntrypointBody entry plan).run {}).2.instructions.size := by
  have frame := (lowerEntrypointBody_preserves entry plan {}).instructions
  simpa using frame

private theorem bind_ok (first : Except ε α) (next : α → Except ε β) (value : β) :
    Except.bind first next = .ok value ↔
      ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp [Except.bind]

private theorem mapM_length {function : α → Except String β} {values : List α}
    {results : List β} (success : values.mapM function = .ok results) :
    results.length = values.length := by
  induction values generalizing results with
  | nil => cases success; rfl
  | cons value rest ih =>
    simp only [List.mapM_cons, bind, bind_ok] at success
    rcases success with ⟨first, firstResult, tail, tailResult, equal⟩
    cases equal
    simp only [List.length_cons, ih tailResult]

/-- Strict native decoding connects the actual accepted instruction vector to
the list of relation instructions. The plan is extracted from accepted lowering. -/
theorem lowerEntrypoint_instruction_count (state : List StateDecl)
    (entry : Entrypoint) (json : Json) (program : Program)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions.size =
        program.instructions.length := by
  obtain ⟨plan, planAccepted, bodyInstructions⟩ :=
    Zkir.lowerEntrypoint_instructions state entry json lowered
  obtain ⟨instructions, parsed, decodedInstructions⟩ :=
    ScalarValidation.decode_result decoded
  rw [bodyInstructions] at parsed
  have instructionsEqual :
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions =
        instructions := by
    injection parsed
  refine ⟨plan, planAccepted, ?_⟩
  calc
    ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.instructions.size =
        instructions.size := congrArg Array.size instructionsEqual
    _ = instructions.toList.length := by simp
    _ = program.instructions.length := (mapM_length decodedInstructions).symm

/-- Actual producer admission bounds the allocated names by the native
instruction limit, using the exact plan and vector from the accepted body. -/
theorem lowerEntrypoint_budget (state : List StateDecl) (entry : Entrypoint)
    (json : Json) (program : Program)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok program) :
    ∃ plan, Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      ((Zkir.lowerEntrypointBody (Passes.pruneEntrypoint entry) plan).run {}).2.next ≤
        maxInstructions := by
  obtain ⟨plan, planAccepted, instructionCount⟩ :=
    lowerEntrypoint_instruction_count state entry json program lowered decoded
  obtain ⟨acceptedPlan, _, acceptedPlanOk, _, producerAccepted⟩ :=
    GenericStateLowering.lowerEntrypoint_validated state entry json lowered
  have samePlan : plan = acceptedPlan := by
    rw [planAccepted] at acceptedPlanOk
    injection acceptedPlanOk
  cases samePlan
  have instructionBound := ScalarAdmission.instruction_bound producerAccepted decoded
  refine ⟨plan, planAccepted, ?_⟩
  have allocated := lowerEntrypointBody_allocated (Passes.pruneEntrypoint entry) plan
  rw [instructionCount] at allocated
  exact Nat.le_trans allocated instructionBound

end Nightlean.Verification.GenericStateLedgerAllocation
