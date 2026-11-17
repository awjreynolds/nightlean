import Nightlean.Verification.GenericStateConverseNativeTrace
import Nightlean.Verification.GenericStateCheckedSchedule

namespace Nightlean.Verification.GenericStateConverseCheckedPlan
open Backend NativeRelation NativeState

/-- Exact compiled chunks and the evaluated source-order segments are the
same operation list before and after interpretation. -/
theorem evaluated_chunks_mapM (state : List StateDecl)
    (ctx : EvalContext) (env : EvalEnv) (effects : List Effect)
    (chunks : List (List Impact.Op)) (segments : List (List Op))
    (aligned : GenericStateAdmission.AlignedChunks state effects chunks)
    (evaluated : GenericStateAdmission.EvaluatedChunks state ctx env
      effects segments) :
    chunks.mapM (fun chunk => chunk.mapM (GenericStateOps.evalOp ctx env)) =
      .ok segments := by
  induction aligned generalizing segments with
  | nil =>
    cases evaluated
    rfl
  | cons first remaining ih =>
    cases evaluated with
    | cons base compiled result tail =>
      obtain ⟨expectedBase, expectedCompiled, shape⟩ := first
      rw [expectedCompiled] at compiled
      have same := Except.ok.inj compiled
      subst base
      simp only [List.mapM_cons]
      rw [← shape, result, ih _ tail]
      rfl

private theorem mapM_flatten_ok (f : α → Except ε β)
    (chunks : List (List α)) (segments : List (List β))
    (accepted : chunks.mapM (fun chunk => chunk.mapM f) = .ok segments) :
    chunks.flatten.mapM f = .ok segments.flatten := by
  induction chunks generalizing segments with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst segments
    rfl
  | cons head tail ih =>
    simp only [List.mapM_cons] at accepted
    cases first : head.mapM f with
    | error message => simp [first, bind, Except.bind] at accepted
    | ok headValues =>
      cases later : tail.mapM (fun chunk => chunk.mapM f) with
      | error message => simp [first, later, bind, Except.bind] at accepted
      | ok tailValues =>
        simp [first, later, bind, Except.bind] at accepted
        simp only [pure, Except.pure, Except.ok.injEq] at accepted
        subst segments
        simp only [List.flatten_cons, List.mapM_append, first,
          ih tailValues later, bind, Except.bind, pure, Except.pure]

theorem eval_plan_of_constructed_chunks (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv)
    (segments : List (List Op)) (publicOps : List Op)
    (accepted : Impact.lower state entry = .ok plan)
    (prefixEval : (Impact.publicInputPlan entry.circuit.inputs {}).operations.mapM
      (GenericStateOps.evalOp ctx env) = .ok publicOps)
    (effectsEval : GenericStateAdmission.EvaluatedChunks state ctx env
      entry.effects segments) :
    GenericStateOps.evalPlan ctx env plan =
      .ok (publicOps ++ segments.flatten) := by
  obtain ⟨chunks, chunksAccepted, operationsShape⟩ :=
    GenericStateAdmission.lower_effect_chunks state entry plan accepted
  have aligned := GenericStateAdmission.effectChunks_aligned state entry.effects
    chunks chunksAccepted
  have chunkEval := evaluated_chunks_mapM state ctx env entry.effects chunks
    segments aligned effectsEval
  have effectEval := mapM_flatten_ok (GenericStateOps.evalOp ctx env)
    chunks segments chunkEval
  unfold GenericStateOps.evalPlan
  rw [operationsShape, List.mapM_append, prefixEval, effectEval]
  rfl

/-- The full production plan checks in the native VM after prefix evaluation
and the constructed effect trace. This lemma consumes no source result oracle. -/
theorem checked_of_constructed_trace (state : List StateDecl)
    (entry : Entrypoint) (plan : Impact.Plan)
    (ctx : EvalContext) (values : EvalEnv) (witness : Assignment)
    (slots finalSlots : List Slot) (publicCells finalReads : List Cell)
    (segments : List (List Op)) (publicOps : List Op)
    (accepted : Impact.lower state entry = .ok plan)
    (prefixEval : (Impact.publicInputPlan entry.circuit.inputs {}).operations.mapM
      (GenericStateOps.evalOp ctx
        (GenericStateCheckedSchedule.outputCandidates ctx entry values ++
          GenericStateInputValues.decodeReads
            (plan.reads.drop
              ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
            witness)) = .ok publicOps)
    (effectsEval : GenericStateAdmission.EvaluatedChunks state ctx
      (GenericStateCheckedSchedule.outputCandidates ctx entry values ++
        GenericStateInputValues.decodeReads
          (plan.reads.drop
            ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
          witness) entry.effects segments)
    (prefixRun : NativeState.run publicOps
      (GenericStateEncoding.initial slots) =
        some ⟨[.vector slots], publicCells⟩)
    (trace : GenericStateVM.RunsChunks segments
      ⟨[.vector slots], publicCells⟩
      ⟨[.vector finalSlots], finalReads⟩) :
    GenericStateCheckedSchedule.CheckedPlan ctx entry plan values witness
      slots ⟨[.vector finalSlots], finalReads⟩ := by
  obtain ⟨chunks, chunksAccepted, operationsShape⟩ :=
    GenericStateAdmission.lower_effect_chunks state entry plan accepted
  have aligned := GenericStateAdmission.effectChunks_aligned state entry.effects
    chunks chunksAccepted
  have chunkEval := evaluated_chunks_mapM state ctx
    (GenericStateCheckedSchedule.outputCandidates ctx entry values ++
      GenericStateInputValues.decodeReads
        (plan.reads.drop
          ((entry.circuit.inputs.filter (·.visibility == .«public»)).length)) witness)
    entry.effects chunks segments aligned effectsEval
  have effectEval : chunks.flatten.mapM (GenericStateOps.evalOp ctx
      (GenericStateCheckedSchedule.outputCandidates ctx entry values ++
        GenericStateInputValues.decodeReads
          (plan.reads.drop
            ((entry.circuit.inputs.filter (·.visibility == .«public»)).length))
          witness)) = .ok segments.flatten :=
    mapM_flatten_ok _ chunks segments chunkEval
  have effectRun :=
    (GenericStateVM.run_chunks_iff segments
      ⟨[.vector slots], publicCells⟩
      ⟨[.vector finalSlots], finalReads⟩).mpr trace
  unfold GenericStateCheckedSchedule.CheckedPlan GenericStateOps.evalPlan
  rw [operationsShape, List.mapM_append, prefixEval, effectEval]
  change NativeState.run (publicOps ++ segments.flatten)
    (GenericStateEncoding.initial slots) =
      some ⟨[.vector finalSlots], finalReads⟩
  rw [NativeState.run_append, prefixRun]
  exact effectRun

end Nightlean.Verification.GenericStateConverseCheckedPlan
