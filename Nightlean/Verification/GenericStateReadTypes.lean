import Nightlean.Verification.GenericStateTypeAdmission

namespace Nightlean.Verification.GenericStateReadTypes
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private def effectReadTypes : Effect → List Ty
  | .readCell _ _ ty => [ty]
  | .requireAbsent .. => [.bool]
  | _ => []

private theorem appendEffect_readTypes (state : List StateDecl)
    (effect : Effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffect state effect before = .ok after) :
    after.reads.map (·.ty) = before.reads.map (·.ty) ++ effectReadTypes effect := by
  have same :
      (fun plan => plan.reads.map (·.ty)) <$> Impact.appendEffect state effect before =
      (fun _ => before.reads.map (·.ty) ++ effectReadTypes effect) <$>
        Impact.appendEffect state effect before := by
    cases effect <;>
      simp only [Impact.appendEffect, effectReadTypes, map_bind,
        LawfulApplicative.map_pure, List.map_append, List.map_cons,
        List.map_nil, List.append_nil] <;> rfl
  rw [accepted] at same
  exact Except.ok.inj same

private theorem appendEffects_readTypes (state : List StateDecl)
    (effects : List Effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffects state effects before = .ok after) :
    after.reads.map (·.ty) = before.reads.map (·.ty) ++ effects.flatMap effectReadTypes := by
  induction effects generalizing before with
  | nil =>
    change Except.ok before = .ok after at accepted
    cases accepted
    simp
  | cons effect rest ih =>
    simp only [Impact.appendEffects, List.foldlM_cons, bind_ok] at accepted
    obtain ⟨middle, first, later⟩ := accepted
    rw [ih middle later, appendEffect_readTypes state effect before middle first]
    simp [List.append_assoc]

private theorem forIn_state_extract
    (body : α → σ → Except ε (ForInStep σ)) (property : α → Prop)
    (values : List α) (initial final : σ)
    (actions : ∀ value before step, body value before = .ok step →
      ∃ after, step = .yield after ∧ property value)
    (success : forIn values initial body = .ok final) :
    ∀ value ∈ values, property value := by
  induction values generalizing initial with
  | nil => simp
  | cons value rest ih =>
    rw [List.forIn_cons] at success
    cases checked : body value initial with
    | error message => simp [checked, bind, Except.bind] at success
    | ok step =>
      obtain ⟨after, equal, holds⟩ := actions value initial step checked
      subst step
      simp only [checked, bind, Except.bind] at success
      intro found member
      rcases List.mem_cons.mp member with equal | member
      · simpa [equal] using holds
      · exact ih after success found member

private def validationStep (span : SourceSpan) (env : TypeEnv)
    (checked : Except String (Option (String × Ty))) :
    Except Diagnostic (ForInStep TypeEnv) :=
  match checked with
  | .error message => do
    throw {span, message}
    pure (.yield env)
  | .ok none => pure (.yield env)
  | .ok (some (name, ty)) =>
    if (env.lookup name).isSome then do
      throw {span, message := s!"state read shadows '{name}'"}
      pure (.yield (env ++ [(name, ty)]))
    else pure (.yield (env ++ [(name, ty)]))

private theorem validationStep_yields (span : SourceSpan) (env : TypeEnv)
    (checked : Except String (Option (String × Ty))) (step : ForInStep TypeEnv)
    (success : validationStep span env checked = .ok step) :
    ∃ after, step = .yield after := by
  cases checked with
  | error message => simp [validationStep, throw, throwThe, bind, Except.bind] at success
  | ok result =>
    cases result with
    | none =>
      change Except.ok (.yield env) = .ok step at success
      exact ⟨env, (Except.ok.inj success).symm⟩
    | some pair =>
      rcases pair with ⟨name, ty⟩
      simp only [validationStep] at success
      split at success
      · simp [throw, throwThe, bind, Except.bind] at success
      · change Except.ok (.yield (env ++ [(name, ty)])) = .ok step at success
        exact ⟨env ++ [(name, ty)], (Except.ok.inj success).symm⟩

private theorem type_beq_sound (left right : Ty) (same : (left == right) = true) :
    left = right := by
  cases left <;> cases right <;> simp_all [BEq.beq, instBEqTy.beq]

private theorem kind_cell_beq_sound (kind : StateKind) (ty : Ty)
    (same : (kind == .cell ty) = true) : kind = .cell ty := by
  cases kind with
  | cell found =>
    have equal : (found == ty) = true := by
      simpa only [BEq.beq, instBEqStateKind.beq] using same
    exact congrArg StateKind.cell (type_beq_sound found ty equal)
  | map key value => simp [BEq.beq, instBEqStateKind.beq] at same

private theorem validated_effect_readTypes (state : List StateDecl)
    (ep : Entrypoint) (plan : Impact.Plan)
    (accepted : Impact.lower state ep = .ok plan) :
    ∀ effect ∈ ep.effects, ∀ ty ∈ effectReadTypes effect,
      ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () := by
  have source := GenericStateAdmission.lower_source_validated state ep plan accepted
  unfold Entrypoint.validate at source
  simp only [bind_ok] at source
  obtain ⟨_, _, _, _, env, _, final, effectsChecked, _⟩ := source
  refine forIn_state_extract _
    (fun effect => ∀ ty ∈ effectReadTypes effect,
      ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok ())
    ep.effects env final ?_ effectsChecked
  intro effect before step success
  have yields : ∃ after, step = .yield after := by
    exact validationStep_yields ep.span before _ step success
  obtain ⟨after, equal⟩ := yields
  refine ⟨after, equal, ?_⟩
  cases effect with
  | readCell name destination ty =>
    change validationStep ep.span before (Except.bind
      (match state.find? (·.name == name) with
      | none => Except.error s!"unknown state '{name}'"
      | some declaration =>
        if declaration.kind == .cell ty then Except.ok ()
        else Except.error s!"state type mismatch for '{name}'")
      (fun _ => Except.ok (some (destination, ty)))) = .ok step at success
    cases found : state.find? (·.name == name) with
    | none => simp [found, validationStep, bind, Except.bind, throw, throwThe] at success
    | some declaration =>
      cases matching : declaration.kind == .cell ty with
      | false => simp [found, matching, validationStep, bind, Except.bind, throw, throwThe] at success
      | true =>
        have typed := GenericStateTypeAdmission.validated_state_types state ep plan accepted
          declaration (List.mem_of_find?_eq_some found)
        have kindEqual := kind_cell_beq_sound declaration.kind ty matching
        rw [kindEqual] at typed
        simpa only [effectReadTypes] using typed
  | readMap name destination keyTy valueTy key => simp [effectReadTypes]
  | require condition => simp [effectReadTypes]
  | writeCell name ty value => simp [effectReadTypes]
  | writeMap name keyTy valueTy key value => simp [effectReadTypes]
  | requireAbsent name keyTy key =>
    simp [effectReadTypes, Ty.validate, Ty.scalarKind, ScalarPolicy.validate]
    rfl

private theorem publicInputPlan_readTypes (inputs : List Input) (initial : Impact.Plan) :
    (Impact.publicInputPlan inputs initial).reads.map (·.ty) =
      initial.reads.map (·.ty) ++
        (inputs.filter (·.visibility == .«public»)).map (·.ty) := by
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
        have one : middle.reads.map (·.ty) = initial.reads.map (·.ty) ++ [ty] := by
          have reads : middle.reads = initial.reads ++ [{name := name, ty := ty}] := rfl
          rw [reads, List.map_append]
          rfl
        rw [one]
        simp [List.append_assoc, BEq.beq, instBEqVisibility.beq]
      | «private» =>
        have one : middle.reads.map (·.ty) = initial.reads.map (·.ty) := rfl
        rw [one]
        rfl

/-- Every actual non-prefix native read has a source-validated type. Generated
absence reads are Bool. This requires no source execution or witness premise. -/
theorem lower_read_types (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    ∀ read ∈ plan.reads.drop
      ((ep.circuit.inputs.filter (·.visibility == .«public»)).length),
      read.ty.validate {poseidon2 := true, stateCells := true, stateMaps := true} = .ok () := by
  have projected := appendEffects_readTypes state ep.effects
    (Impact.publicInputPlan ep.circuit.inputs {}) plan
    (GenericStateAdmission.lower_effect_fold state ep plan accepted)
  rw [publicInputPlan_readTypes] at projected
  simp only [List.map_nil, List.nil_append] at projected
  have sourceTypes := validated_effect_readTypes state ep plan accepted
  intro read member
  have mapped : read.ty ∈ (plan.reads.drop
      ((ep.circuit.inputs.filter (·.visibility == .«public»)).length)).map (·.ty) :=
    List.mem_map_of_mem member
  rw [List.map_drop, projected] at mapped
  simp only [← List.length_map (f := fun input : Input => input.ty),
    List.drop_left] at mapped
  obtain ⟨effect, present, typeMember⟩ := List.mem_flatMap.mp mapped
  exact sourceTypes effect present read.ty typeMember

end Nightlean.Verification.GenericStateReadTypes
