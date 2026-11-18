import Noctium.Verification.GenericStateNativeSchedule
import Noctium.Verification.GenericStateReadTape

namespace Noctium.Verification.GenericStateCheckedSchedule
open Backend NativeRelation ScalarNormalization Backend.Native

/-- Computed output values used when checking the exact native schedule.
Accepted relation soundness later proves the fallback branch unreachable. -/
def outputCandidates (ctx : EvalContext) (entry : Entrypoint)
    (values : EvalEnv) : EvalEnv :=
  (entry.circuit.outputs.mapM (evalOutput ctx values)).toOption.getD [] ++ values

/-- Check the actual Impact plan's evaluated VM operations against the
generic native state machine. This property asks for a checked trace, not a
desired source transition or a desired native successor. -/
def CheckedPlan (ctx : EvalContext) (entry : Entrypoint)
    (plan : Impact.Plan) (values : EvalEnv) (witness : Assignment)
    (slots : List NativeState.Slot) (final : NativeState.Machine) : Prop :=
  ((GenericStateOps.evalPlan ctx
    (outputCandidates ctx entry values ++ GenericStateInputValues.decodeReads
      (plan.reads.drop ((entry.circuit.inputs.filter
        (·.visibility == .«public»)).length)) witness) plan).toOption.bind
    (fun ops => NativeState.run ops (GenericStateEncoding.initial slots))) = some final

/-- Accepted ZKIR satisfaction and an independent checked VM run recover the
real compiler's ordered effect segments and every intermediate machine. -/
theorem accepted_checked_trace (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (witness : Assignment)
    (streams : InputStreams) (publicGroups : List (List Scalar))
    (slots : List NativeState.Slot)
    (final : NativeState.Machine)
    (admittedInputs : CanonicalInputs entry.circuit values witness)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups)
    (plan : Impact.Plan)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (checked : CheckedPlan ctx (Passes.pruneEntrypoint entry) plan
      values witness slots final) :
    ∃ result ops chunks segments publicCells,
      entry.circuit.run ctx values = .ok result ∧
      GenericStateOps.evalPlan ctx
        ((result ++ values) ++ GenericStateInputValues.decodeReads
          (plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
            (·.visibility == .«public»)).length)) witness) plan = .ok ops ∧
      publicGroups = NativeState.groups ops ∧
      GenericStateAdmission.effectChunks state
        (Passes.pruneEntrypoint entry).effects = .ok chunks ∧
      GenericStateAdmission.AlignedChunks state
        (Passes.pruneEntrypoint entry).effects chunks ∧
      GenericStateAdmission.EvaluatedChunks state ctx
        ((result ++ values) ++ GenericStateInputValues.decodeReads
          (plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
            (·.visibility == .«public»)).length)) witness)
        (Passes.pruneEntrypoint entry).effects segments ∧
      GenericStateVM.RunsChunks segments
        ⟨[.vector slots], publicCells⟩ final := by
  obtain ⟨schedulePlan, result, ops, scheduleAccepted, sourceRun,
    evaluated, groups⟩ :=
    GenericStateNativeSchedule.accepted_native_schedule state entry json relation
      ctx hash implementation values witness streams publicGroups admittedInputs
      lowered decoded satisfies
  have samePlan : schedulePlan = plan := by
    rw [planAccepted] at scheduleAccepted
    exact (Except.ok.inj scheduleAccepted).symm
  subst schedulePlan
  have outputEval :=
    (ScalarNormalization.circuit_run_steps ctx entry.circuit values result sourceRun).2
  have candidateValues :
      outputCandidates ctx (Passes.pruneEntrypoint entry) values = result ++ values := by
    simp only [outputCandidates, Passes.pruneEntrypoint, Passes.pruneCircuit]
    rw [outputEval]
    rfl
  have vmChecked : NativeState.run ops
      (GenericStateEncoding.initial slots) = some final := by
    unfold CheckedPlan at checked
    rw [candidateValues, evaluated] at checked
    simpa only [Except.toOption, Option.bind_some] using checked
  obtain ⟨chunks, segments, publicCells, chunksAccepted, aligned,
    _, segmentsAligned, trace⟩ :=
    GenericStateAdmission.lower_checked_trace state
      (Passes.pruneEntrypoint entry) plan ctx
      ((result ++ values) ++ GenericStateInputValues.decodeReads
        (plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
          (·.visibility == .«public»)).length)) witness)
      ops slots final planAccepted evaluated vmChecked
  exact ⟨result, ops, chunks, segments, publicCells, sourceRun, evaluated,
    groups, chunksAccepted, aligned, segmentsAligned, trace⟩

end Noctium.Verification.GenericStateCheckedSchedule
