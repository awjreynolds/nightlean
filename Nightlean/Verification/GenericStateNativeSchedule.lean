import Nightlean.Verification.GenericStateCandidateEnvironment

namespace Nightlean.Verification.GenericStateNativeSchedule
open Backend NativeRelation ScalarNormalization Backend.Native
open GenericStateCircuitParts

/-- Exact production output aliases and accepted expected operation pieces
force evaluation of the same Impact plan to a native VM schedule. -/
theorem expected_native_schedule (state : List StateDecl) (ep : Entrypoint)
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
    ∃ ops, GenericStateOps.evalPlan ctx values plan = .ok ops ∧
      expected.groups.map (List.map (interpret hash witness)) =
        NativeState.groups ops := by
  obtain ⟨actualPlan, actualFrame, _, _, operationFrame,
    actualLower, actualNormalize, _, _, operationsAccepted,
    _, groupsShape, _, _, assertionShape, boundShape⟩ :=
    expectedEntrypoint_parts state ep expected accepted
  have samePlan : actualPlan = plan := by
    rw [lowered] at actualLower
    exact (Except.ok.inj actualLower).symm
  subst actualPlan
  have sameFrame : actualFrame = frame := by
    rw [normalized] at actualNormalize
    exact (Except.ok.inj actualNormalize).symm
  subst actualFrame
  obtain ⟨pieces, piecesAccepted, groupsExact,
    pieceBounds, pieceAssertions⟩ :=
    GenericStateAdmission.expected_operation_groups ep.span frame.1
      plan.operations frame.2.1 operationFrame.1 operationFrame.2.1
      operationFrame.2.2 operationsAccepted
  have allFields : ∀ expression ∈ plan.operations.flatMap Impact.Op.fields,
      expression.validate {poseidon2 := true}
        (GenericStateAdmission.planTypes plan ep) = .ok () := by
    simpa only [Impact.Plan.fields, GenericStateAdmission.planTypes] using
      (GenericStateAdmission.validated_fields plan ep
        (GenericStateAdmission.lower_validated state ep plan lowered))
  have operationFields := GenericStateAdmission.operation_pieces_meaning
    ctx hash implementation witness (GenericStateAdmission.planTypes plan ep)
    frame.1 values environment ep.span plan.operations pieces piecesAccepted
    allFields
    (fun requirement member => bounds requirement (by
      rw [boundShape, pieceBounds]
      exact List.mem_append_left _ (List.mem_append_left _
        (List.mem_append_right _ member))))
    (fun assertion member => assertions assertion (by
      rw [assertionShape, pieceAssertions]
      exact List.mem_append_right _ member))
  obtain ⟨ops, evaluated⟩ := GenericStateOps.evalOperations_of_fields
    ctx values plan.operations _ operationFields
  refine ⟨ops, evaluated, ?_⟩
  have nativeFields := GenericStateAdmission.lower_plan_groups
    state ep plan ctx values ops lowered implementation.modulus evaluated
  rw [operationFields] at nativeFields
  have same := Except.ok.inj nativeFields
  simpa only [groupsShape, groupsExact, List.map_map, Function.comp_def]
    using same

/-- Satisfaction of the actual emitted and strictly decoded relation fixes
every native VM operation group for the compiler's exact ordered plan. -/
theorem accepted_native_schedule (state : List StateDecl)
    (entry : Entrypoint) (json : Lean.Json) (relation : Program)
    (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash)
    (values : EvalEnv) (witness : Assignment)
    (streams : InputStreams) (publicGroups : List (List Scalar))
    (admitted : CanonicalInputs entry.circuit values witness)
    (lowered : Zkir.lowerEntrypoint state entry = .ok json)
    (decoded : NativeRelationJson.decode json = .ok relation)
    (satisfies : CircuitSatisfies hash relation streams witness publicGroups) :
    ∃ plan result ops,
      Impact.lower state (Passes.pruneEntrypoint entry) = .ok plan ∧
      entry.circuit.run ctx values = .ok result ∧
      GenericStateOps.evalPlan ctx
        ((result ++ values) ++ GenericStateInputValues.decodeReads
          (plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
            (·.visibility == .«public»)).length)) witness)
        plan = .ok ops ∧
      publicGroups = NativeState.groups ops := by
  obtain ⟨plan, frame, result, planAccepted, sourceRun,
    normalized, environment⟩ :=
    GenericStateCandidateEnvironment.accepted_candidate_environment
      state entry json relation ctx hash implementation values witness
      streams publicGroups admitted lowered decoded satisfies
  obtain ⟨samePlan, expected, samePlanAccepted, expectedAccepted,
    groupValues, bounds, assertions⟩ :=
    GenericStateLowering.accepted_relation_groups_self state entry json
      relation hash witness streams publicGroups lowered decoded satisfies
  have planEqual : samePlan = plan := by
    rw [planAccepted] at samePlanAccepted
    exact (Except.ok.inj samePlanAccepted).symm
  subst samePlan
  obtain ⟨ops, evaluated, groups⟩ := expected_native_schedule state
    (Passes.pruneEntrypoint entry) expected expectedAccepted
    plan frame planAccepted normalized ctx hash implementation witness
    ((result ++ values) ++ GenericStateInputValues.decodeReads
      (plan.reads.drop (((Passes.pruneEntrypoint entry).circuit.inputs.filter
        (·.visibility == .«public»)).length)) witness)
    environment bounds assertions
  exact ⟨plan, result, ops, planAccepted, sourceRun,
    evaluated, groupValues.trans groups⟩

end Nightlean.Verification.GenericStateNativeSchedule
