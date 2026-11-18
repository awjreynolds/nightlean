import Noctium.Verification.GenericStateConverseInitialEnvironment
import Noctium.Verification.GenericStateReadCellEvaluation

namespace Noctium.Verification.GenericStateConversePublicPrefix
open Backend NativeRelation ScalarNormalization NativeState

private def inputOperations (input : Input) : List Impact.Op :=
  if input.visibility == .«public» then
    let value := Impact.Aligned.field
      (GenericStateReadCellEvaluation.readExpression input.ty input.name)
    [.push value, .popeq value]
  else []

private theorem publicInputPlan_operations (inputs : List Input) (initial : Impact.Plan) :
    (Impact.publicInputPlan inputs initial).operations =
      initial.operations ++ inputs.flatMap inputOperations := by
  induction inputs generalizing initial with
  | nil => simp [Impact.publicInputPlan]
  | cons input rest ih =>
    let middle := Impact.publicInputPlan [input] initial
    have foldShape : Impact.publicInputPlan (input :: rest) initial =
        Impact.publicInputPlan rest middle := rfl
    rw [foldShape, ih middle]
    cases input with
    | mk name ty visibility span =>
      cases visibility with
      | «public» =>
        have one : middle.operations = initial.operations ++
            inputOperations {name, ty, visibility := .«public», span} := rfl
        rw [one]
        simp [List.append_assoc]
      | «private» =>
        have one : middle.operations = initial.operations := rfl
        rw [one]
        rfl

private theorem inputs_evaluate (inputs : List Input) (ctx : EvalContext) (env : EvalEnv)
    (modulus : ctx.modulus = Field.modulus)
    (canonical : ∀ input ∈ inputs, ∃ value : input.ty.Denote,
      env.lookup input.name = some (Value.pack input.ty value) ∧ Canonical input.ty value) :
    ∃ native, (inputs.flatMap inputOperations).mapM
      (GenericStateOps.evalOp ctx env) = .ok native := by
  induction inputs with
  | nil => exact ⟨[], rfl⟩
  | cons input rest ih =>
    obtain ⟨remaining, tail⟩ := ih (fun found member => canonical found (by simp [member]))
    obtain ⟨value, lookup, typed⟩ := canonical input (by simp)
    cases input with
    | mk name ty visibility span =>
      cases visibility with
      | «private» =>
        exact ⟨remaining, tail⟩
      | «public» =>
        have readValue := GenericStateReadCellEvaluation.readExpression_eval ctx env
          name ty value lookup modulus typed
        refine ⟨[NativeState.Op.push (field (scalar (number ty value))) false,
          .popeq (field (scalar (number ty value)))] ++ remaining, ?_⟩
        rw [List.flatMap_cons, List.mapM_append]
        have first : (inputOperations {name, ty, visibility := .«public», span}).mapM
            (GenericStateOps.evalOp ctx env) =
            .ok [NativeState.Op.push (field (scalar (number ty value))) false,
              .popeq (field (scalar (number ty value)))] := by
          simp [inputOperations, BEq.beq, instBEqVisibility.beq,
            GenericStateOps.evalOp, GenericStateOps.evalAligned,
            readValue, Except.map, Functor.map] <;> rfl
        rw [first, tail]
        rfl

private theorem lookup_none_of_absent_name (items : List (String × α))
    (name : String) (absent : name ∉ items.map Prod.fst) : items.lookup name = none := by
  apply List.lookup_eq_none_iff.mpr
  intro pair present
  have different : name ≠ pair.1 := by
    intro equal
    exact absent (List.mem_map.mpr ⟨pair, present, equal.symm⟩)
  simp [different]

/-- Actual successful source circuit results do not shadow any original input.
Appending future candidate reads therefore preserves every canonical input. -/
theorem source_input_lookup (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (values outputs future : EvalEnv)
    (inputs : Assignment) (accepted : Impact.lower state ep = .ok plan)
    (admitted : CanonicalInputs ep.circuit values inputs)
    (source : ep.circuit.run ctx values = .ok outputs) :
    ∀ input ∈ ep.circuit.inputs, ∃ value : input.ty.Denote,
      ((outputs ++ values) ++ future).lookup input.name = some (Value.pack input.ty value) ∧
      Canonical input.ty value := by
  have valid := GenericStateAdmission.lower_circuit_validated state ep plan accepted
  obtain ⟨_, evaluated⟩ := circuit_run_steps ctx ep.circuit values outputs source
  have names := GenericStateReadFreshness.source_outputs_names ctx values ep.circuit.outputs outputs evaluated
  intro input present
  obtain ⟨value, lookup, typed⟩ := admitted.complete input present
  have noOutput : input.name ∉ outputs.map Prod.fst := by
    intro member
    rw [names] at member
    obtain ⟨output, outputMember, equal⟩ := List.mem_map.mp member
    have unused := GenericStateAliases.validated_outputs_unshadowed ep.circuit valid output outputMember
    have different := List.lookup_eq_none_iff.mp unused (input.name, input.ty)
      (List.mem_map.mpr ⟨input, present, rfl⟩)
    simp [equal] at different
  have outputNone := lookup_none_of_absent_name outputs input.name noOutput
  refine ⟨value, ?_, typed⟩
  simp [List.lookup_append, outputNone, lookup]

/-- Original source success constructs the actual public-input prefix and its
successful native execution. Future read bindings need no desired VM premise. -/
theorem source_public_prefix (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (values outputs future : EvalEnv)
    (inputs : Assignment) (stack : List Node) (reads : List Cell)
    (accepted : Impact.lower state ep = .ok plan)
    (admitted : CanonicalInputs ep.circuit values inputs)
    (source : ep.circuit.run ctx values = .ok outputs)
    (modulus : ctx.modulus = Field.modulus) :
    ∃ native cells,
      (Impact.publicInputPlan ep.circuit.inputs {}).operations.mapM
        (GenericStateOps.evalOp ctx ((outputs ++ values) ++ future)) = .ok native ∧
      native = cells.flatMap (fun cell => [NativeState.Op.push cell false, .popeq cell]) ∧
      run native ⟨stack, reads⟩ = some ⟨stack, reads ++ cells⟩ := by
  obtain ⟨native, evaluated⟩ := inputs_evaluate ep.circuit.inputs ctx
    ((outputs ++ values) ++ future) modulus
    (source_input_lookup state ep plan ctx values outputs future inputs accepted admitted source)
  have actual : (Impact.publicInputPlan ep.circuit.inputs {}).operations.mapM
      (GenericStateOps.evalOp ctx ((outputs ++ values) ++ future)) = .ok native := by
    simpa only [publicInputPlan_operations, List.nil_append] using evaluated
  obtain ⟨cells, shape, checked⟩ := GenericStateAdmission.public_prefix_run
    ep.circuit.inputs ctx ((outputs ++ values) ++ future) native stack reads actual
  exact ⟨native, cells, actual, shape, checked⟩

end Noctium.Verification.GenericStateConversePublicPrefix
