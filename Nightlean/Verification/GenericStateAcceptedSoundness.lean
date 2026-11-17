import Nightlean.Verification.GenericStateEffectFold
import Nightlean.Verification.GenericStateCheckedSchedule
import Nightlean.Verification.GenericStateInitialFrame
import Nightlean.Verification.GenericStateReadCandidates
import Nightlean.Verification.GenericStateGuardSoundness

namespace Nightlean.Verification.GenericStateAcceptedSoundness
open Backend NativeRelation ScalarNormalization NativeState
open GenericStateEffectStep

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- The actual lowerer runs mandatory disclosure validation before producing
an Impact plan. This retains the original source entrypoint's public sink gate. -/
theorem lower_disclosure (state : List StateDecl) (entry : Entrypoint)
    (plan : Impact.Plan)
    (accepted : Impact.lower state entry = .ok plan) :
    Disclosure.entrypoint entry = .ok () := by
  unfold Impact.lower at accepted
  simp only [bind_ok] at accepted
  rcases accepted with ⟨_, _, _, disclosure, _⟩
  exact disclosure

/-- An arbitrary satisfying witness for the actual, strictly decoded ZKIR
relation, together with independent state admission and a checked native VM
run, forces the original entrypoint to succeed. Its successor has exactly the
root array left by the VM. Internal computed outputs are returned separately
from the VM's public read tape. -/
theorem accepted_entrypoint_run_sound (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (witness : Assignment)
    (streams : InputStreams) (publicGroups : List (List Scalar))
    (admittedInputs : CanonicalInputs entry.circuit values witness)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups)
    (initialState : LedgerState) (slots : List NativeState.Slot)
    (admittedState : GenericStateEncoding.AdmittedState state initialState slots)
    (plan : Impact.Plan)
    (planAccepted : Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan)
    (final : NativeState.Machine)
    (checked : GenericStateCheckedSchedule.CheckedPlan ctx
      (Passes.pruneEntrypoint entry) plan values witness slots final) :
    ∃ outputs next nextSlots finalReads,
      entry.run ctx values initialState = .ok (outputs, next) ∧
      GenericStateEncoding.encodeState state next = some nextSlots ∧
      final = ⟨[.vector nextSlots], finalReads⟩ := by
  let ep := Passes.pruneEntrypoint entry
  let reads := plan.reads.drop
    ((ep.circuit.inputs.filter (·.visibility == .«public»)).length)
  let complete := ((GenericStateCheckedSchedule.outputCandidates ctx ep values) ++
    GenericStateInputValues.decodeReads reads witness)
  obtain ⟨result, ops, chunks, segments, publicCells, circuitRun,
    planEval, groups, chunksAccepted, aligned, evaluated, trace⟩ :=
    GenericStateCheckedSchedule.accepted_checked_trace state entry json
      relation ctx hash implementation values witness streams publicGroups
      slots final admittedInputs lowered decoded satisfies plan planAccepted checked
  have prunedRun : ep.circuit.run ctx values = .ok result := by
    simpa only [ep, Passes.pruneEntrypoint, Passes.pruneCircuit_run]
      using circuitRun
  have outputEval :=
    (ScalarNormalization.circuit_run_steps ctx entry.circuit values result circuitRun).2
  have completeEq : complete = (result ++ values) ++
      GenericStateInputValues.decodeReads reads witness := by
    simp only [complete, GenericStateCheckedSchedule.outputCandidates,
      ep, Passes.pruneEntrypoint, Passes.pruneCircuit]
    rw [outputEval]
    rfl
  rw [← completeEq] at evaluated
  obtain ⟨samePlan, initialResult, sameAccepted, sameRun, initialAgrees⟩ :=
    GenericStateInitialFrame.accepted_initial_agreement state entry json relation
      ctx hash implementation values witness streams publicGroups admittedInputs
      lowered decoded satisfies
  have planEq : samePlan = plan := by
    rw [planAccepted] at sameAccepted
    exact (Except.ok.inj sameAccepted).symm
  subst samePlan
  have resultEq : initialResult = result := by
    rw [circuitRun] at sameRun
    exact (Except.ok.inj sameRun).symm
  subst initialResult
  have initialAgreement : GenericStatePrefixEnvironment.AgreesOnTypes
      (GenericStateEffectValidation.initialEffectTypeEnv ep)
      (result ++ values) complete := by
    simpa only [GenericStateEffectValidation.initialEffectTypeEnv,
      completeEq, ep] using initialAgrees
  obtain ⟨candidatePlan, candidateAccepted, typedBounded⟩ :=
    GenericStateReadAdmission.accepted_read_candidates state entry json relation
      hash witness streams publicGroups lowered decoded satisfies
  have candidateEq : candidatePlan = plan := by
    rw [planAccepted] at candidateAccepted
    exact (Except.ok.inj candidateAccepted).symm
  subst candidatePlan
  obtain ⟨guardPlan, guardResult, guardAccepted, guardRun, guardsTrue⟩ :=
    GenericStateGuardSoundness.accepted_requires_sound state entry json relation
      ctx hash implementation values witness streams publicGroups admittedInputs
      lowered decoded satisfies
  have guardEq : guardPlan = plan := by
    rw [planAccepted] at guardAccepted
    exact (Except.ok.inj guardAccepted).symm
  subst guardPlan
  have guardResultEq : guardResult = result := by
    rw [circuitRun] at guardRun
    exact (Except.ok.inj guardRun).symm
  subst guardResult
  have prunedAdmission : CanonicalInputs ep.circuit values witness :=
    ⟨admittedInputs.unique, admittedInputs.declared,
      admittedInputs.complete, admittedInputs.binding⟩
  have allCandidates : ∀ effect ∈ ep.effects,
      ReadCandidate effect complete := by
    intro effect member
    cases effect with
    | readCell name destination ty =>
      rw [completeEq]
      exact GenericStateReadCandidates.readCell_candidate state ep plan ctx
        values result witness name destination ty prunedAdmission planAccepted
        prunedRun member typedBounded
    | readMap name destination keyTy valueTy key => trivial
    | require condition => trivial
    | writeCell name ty value => trivial
    | writeMap name keyTy valueTy key value => trivial
    | requireAbsent name keyTy key => trivial
  have allGuards : ∀ effect ∈ ep.effects,
      GuardTrue ctx effect complete := by
    intro effect member
    cases effect with
    | require condition =>
      rw [completeEq]
      exact guardsTrue condition member
    | readCell name destination ty => trivial
    | readMap name destination keyTy valueTy key => trivial
    | writeCell name ty value => trivial
    | writeMap name keyTy valueTy key value => trivial
    | requireAbsent name keyTy key => trivial
  obtain ⟨finalTypes, validated⟩ :=
    GenericStateEffectValidation.lower_validated_effects state ep plan planAccepted
  obtain ⟨finalEnv, next, nextSlots, finalReads,
    sourceFold, nextEncoded, finalShape, _⟩ :=
    GenericStateEffectFold.checked_effects_fold ctx state ep.effects
      (GenericStateEffectValidation.initialEffectTypeEnv ep) finalTypes
      (result ++ values) complete initialState slots publicCells segments final
      validated evaluated trace allCandidates allGuards initialAgreement
      admittedState.encoded admittedState.distinctDeclarations
      admittedState.slotBound implementation.modulus
  have sourceEffects : runEffects ctx ep.effects (result ++ values)
      initialState = .ok next := by
    rw [SourceEffects.runEffects_eq_fold, sourceFold]
    rfl
  have disclosure : Disclosure.entrypoint ep = .ok () :=
    lower_disclosure state ep plan planAccepted
  have prunedEntry : ep.run ctx values initialState = .ok (result, next) := by
    simp only [Entrypoint.run, disclosure, prunedRun, sourceEffects,
      bind, Except.bind]
    rfl
  refine ⟨result, next, nextSlots, finalReads, ?_, nextEncoded, finalShape⟩
  simpa only [ep, Passes.pruneEntrypoint_run] using prunedEntry

end Nightlean.Verification.GenericStateAcceptedSoundness
