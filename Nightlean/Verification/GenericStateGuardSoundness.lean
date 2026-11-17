import Nightlean.Verification.GenericStateCandidateEnvironment
import Nightlean.Verification.GenericStateGuardTape

namespace Nightlean.Verification.GenericStateGuardSoundness
open Backend NativeRelation ScalarNormalization Backend.Native
open GenericStateCircuitParts

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- The production plan validator checks every emitted guard expression
under the exact full type environment used by native normalization. -/
theorem validated_guards (plan : Impact.Plan) (ep : Entrypoint)
    (accepted : plan.validate ep = .ok ()) :
    validateConstraints {poseidon2 := true}
      (GenericStateAdmission.planTypes plan ep) ep.span plan.guards = .ok () := by
  unfold Impact.Plan.validate at accepted
  simp only [bind_ok] at accepted
  obtain ⟨_, _, _, guardsAccepted, _⟩ := accepted
  have checks : ∀ guard ∈ plan.guards,
      guard.validate {poseidon2 := true}
        (GenericStateAdmission.planTypes plan ep) = .ok () := by
    refine GenericStateAliases.forIn_extract _
      (fun guard => guard.validate {poseidon2 := true}
        (GenericStateAdmission.planTypes plan ep) = .ok ())
      plan.guards ?_ guardsAccepted
    intro guard step success
    change (do
      let _ ← guard.validate {poseidon2 := true}
        (GenericStateAdmission.planTypes plan ep)
      pure (ForInStep.yield PUnit.unit)) = .ok step at success
    cases checked : guard.validate {poseidon2 := true}
        (GenericStateAdmission.planTypes plan ep) with
    | error message => simp [checked, bind, Except.bind] at success
    | ok checkedUnit =>
      cases checkedUnit
      simp only [checked, bind, Except.bind] at success
      exact ⟨(Except.ok.inj success).symm, rfl⟩
  have runChecked (guards : List (Expr .bool))
      (all : ∀ guard ∈ guards, guard.validate {poseidon2 := true}
        (GenericStateAdmission.planTypes plan ep) = .ok ()) :
      validateConstraints {poseidon2 := true}
        (GenericStateAdmission.planTypes plan ep) ep.span guards = .ok () := by
    induction guards with
    | nil => rfl
    | cons guard rest ih =>
      have first := all guard (by simp)
      have later : ∀ item ∈ rest,
          item.validate {poseidon2 := true}
            (GenericStateAdmission.planTypes plan ep) = .ok () := by
        intro item member
        exact all item (by simp [member])
      simpa [validateConstraints, first] using ih later
  exact runChecked plan.guards checks

/-- Independent expected assertions force every actual Impact guard to
evaluate to true under the typed candidate environment. -/
theorem expected_guards_sound (state : List StateDecl) (ep : Entrypoint)
    (expected : Expected) (accepted : expectedEntrypoint state ep = .ok expected)
    (plan : Impact.Plan) (frame : OutputFrame)
    (lowered : Impact.lower state ep = .ok plan)
    (normalized : normalizeOutputs (initialAliases ep plan)
      ep.circuit.outputs = .ok frame)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (witness : Assignment) (values : EvalEnv)
    (environment : TypedEnvironment hash witness frame.1 values
      (GenericStateAdmission.planTypes plan ep))
    (bounds : ∀ requirement ∈ expected.bounds,
      (interpret hash witness requirement.1).val ≤ requirement.2)
    (assertions : ∀ term ∈ expected.assertions,
      interpret hash witness term = one) :
    runConstraints ctx values plan.guards = .ok () := by
  obtain ⟨actualPlan, actualFrame, conditions, guards, operationFrame,
    actualLower, actualNormalize, _, guardsAccepted, _,
    _, _, _, _, assertionShape, boundShape⟩ :=
    expectedEntrypoint_parts state ep expected accepted
  have samePlan : actualPlan = plan := by
    rw [lowered] at actualLower
    exact (Except.ok.inj actualLower).symm
  subst actualPlan
  have sameFrame : actualFrame = frame := by
    rw [normalized] at actualNormalize
    exact (Except.ok.inj actualNormalize).symm
  subst actualFrame
  apply ScalarNormalization.constraints_sound ctx hash implementation witness
    (GenericStateAdmission.planTypes plan ep) frame.1 values environment
    ep.span plan.guards guards
  · exact validated_guards plan ep
      (GenericStateAdmission.lower_validated state ep plan lowered)
  · exact guardsAccepted
  · intro requirement member
    apply bounds requirement
    rw [boundShape]
    exact List.mem_append_right _ member
  · intro term member
    apply assertions term
    rw [assertionShape]
    exact List.mem_append_left _ (List.mem_append_right _ member)

theorem runConstraints_all (ctx : EvalContext) (values : EvalEnv)
    (conditions : List (Expr .bool))
    (success : runConstraints ctx values conditions = .ok ()) :
    ∀ condition ∈ conditions, condition.eval ctx values = .ok true := by
  induction conditions with
  | nil => simp
  | cons condition rest ih =>
    cases checked : condition.eval ctx values with
    | error message => simp [runConstraints, checked] at success
    | ok value =>
      cases value with
      | false => simp [runConstraints, checked] at success
      | true =>
        have tail : runConstraints ctx values rest = .ok () := by
          simpa [runConstraints, checked] using success
        intro item member
        rcases List.mem_cons.mp member with equal | member
        · simpa [equal] using checked
        · exact ih tail item member

theorem accepted_guards_sound (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (witness : Assignment)
    (streams : InputStreams) (publicGroups : List (List Scalar))
    (admitted : CanonicalInputs entry.circuit values witness)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ plan result,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      entry.circuit.run ctx values = .ok result ∧
      ∀ guard ∈ plan.guards,
        guard.eval ctx
          ((result ++ values) ++ GenericStateInputValues.decodeReads
            (plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
              (·.visibility == .«public»)).length)) witness) = .ok true := by
  obtain ⟨plan, frame, result, planAccepted, sourceRun,
    normalized, environment⟩ :=
    GenericStateCandidateEnvironment.accepted_candidate_environment state entry
      json relation ctx hash implementation values witness streams publicGroups
      admitted lowered decoded satisfies
  obtain ⟨samePlan, expected, samePlanAccepted, expectedAccepted,
    _, bounds, assertions⟩ :=
    GenericStateLowering.accepted_relation_groups_self state entry json relation
      hash witness streams publicGroups lowered decoded satisfies
  have same : samePlan = plan := by
    rw [planAccepted] at samePlanAccepted
    exact (Except.ok.inj samePlanAccepted).symm
  subst samePlan
  have guards := expected_guards_sound state
    (Passes.pruneEntrypoint entry) expected expectedAccepted plan frame
    planAccepted normalized ctx hash implementation witness
    ((result ++ values) ++ GenericStateInputValues.decodeReads
      (plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
        (·.visibility == .«public»)).length)) witness)
    environment bounds assertions
  exact ⟨plan, result, planAccepted, sourceRun,
    runConstraints_all ctx _ plan.guards guards⟩

theorem accepted_requires_sound (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (witness : Assignment)
    (streams : InputStreams) (publicGroups : List (List Scalar))
    (admitted : CanonicalInputs entry.circuit values witness)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ plan result,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      entry.circuit.run ctx values = .ok result ∧
      ∀ condition, Effect.require condition ∈ (Passes.pruneEntrypoint entry).effects →
        condition.eval ctx
          ((result ++ values) ++ GenericStateInputValues.decodeReads
            (plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
              (·.visibility == .«public»)).length)) witness) = .ok true := by
  obtain ⟨plan, result, accepted, source, guards⟩ :=
    accepted_guards_sound state entry json relation ctx hash implementation
      values witness streams publicGroups admitted lowered decoded satisfies
  refine ⟨plan, result, accepted, source, ?_⟩
  intro condition member
  exact GenericStateGuardTape.lower_require_guard_true state
    (Passes.pruneEntrypoint entry) plan ctx _ accepted guards condition member

end Nightlean.Verification.GenericStateGuardSoundness
