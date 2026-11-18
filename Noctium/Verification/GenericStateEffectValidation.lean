import Noctium.Verification.GenericStateTypeAdmission

namespace Noctium.Verification.GenericStateEffectValidation
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem type_beq_true (left right : Ty) (same : (left == right) = true) :
    left = right := by
  cases left <;> cases right <;> simp_all [BEq.beq, instBEqTy.beq]

private theorem kind_cell_beq_true (kind : StateKind) (ty : Ty)
    (same : (kind == .cell ty) = true) : kind = .cell ty := by
  cases kind with
  | cell found =>
    have equal : (found == ty) = true := by
      simpa only [BEq.beq, instBEqStateKind.beq] using same
    exact congrArg StateKind.cell (type_beq_true found ty equal)
  | map key value => simp [BEq.beq, instBEqStateKind.beq] at same

private theorem kind_map_beq_true (kind : StateKind) (keyTy valueTy : Ty)
    (same : (kind == .map keyTy valueTy) = true) :
    kind = .map keyTy valueTy := by
  cases kind with
  | cell found => simp [BEq.beq, instBEqStateKind.beq] at same
  | map foundKey foundValue =>
    have both : (foundKey == keyTy) = true ∧ (foundValue == valueTy) = true := by
      simpa only [BEq.beq, instBEqStateKind.beq, Bool.and_eq_true] using same
    have equalKey : (foundKey == keyTy) = true := by
      exact both.1
    have equalValue : (foundValue == valueTy) = true := by
      exact both.2
    cases type_beq_true foundKey keyTy equalKey
    cases type_beq_true foundValue valueTy equalValue
    rfl

def stateEffectCaps : Capabilities :=
  {poseidon2 := true, stateCells := true, stateMaps := true}

def HasDeclaration (state : List StateDecl) (name : String)
    (kind : StateKind) : Prop :=
  ∃ declaration,
    state.find? (fun item => item.name == name) = some declaration ∧
      declaration.kind = kind

private def requireDeclaredState (decls : List StateDecl) (name : String)
    (kind : StateKind) : Except String Unit :=
  match decls.find? (·.name == name) with
  | none => .error s!"unknown state '{name}'"
  | some decl => if decl.kind == kind then .ok ()
    else .error s!"state type mismatch for '{name}'"

private def effectCheck (caps : Capabilities) (decls : List StateDecl)
    (env : TypeEnv) : Effect → Except String (Option (String × Ty))
  | .readCell state destination ty => do
      if !caps.stateCells then throw "target lacks state cells"
      requireDeclaredState decls state (.cell ty)
      pure (some (destination, ty))
  | .readMap state destination keyTy valueTy key => do
      if !caps.stateMaps then throw "target lacks state maps"
      requireDeclaredState decls state (.map keyTy valueTy)
      key.validate caps env
      pure (some (destination, valueTy))
  | .require condition => do
      condition.validate caps env
      pure none
  | .writeCell state ty value => do
      if !caps.stateCells then throw "target lacks state cells"
      requireDeclaredState decls state (.cell ty)
      value.validate caps env
      pure none
  | .writeMap state keyTy valueTy key value => do
      if !caps.stateMaps then throw "target lacks state maps"
      requireDeclaredState decls state (.map keyTy valueTy)
      key.validate caps env
      value.validate caps env
      pure none
  | .requireAbsent state keyTy key => do
      if !caps.stateMaps then throw "target lacks state maps"
      match decls.find? (·.name == state) with
      | some {kind := .map found _, ..} =>
        if found != keyTy then throw s!"state key type mismatch for '{state}'"
      | _ => throw s!"unknown map state '{state}'"
      key.validate caps env
      pure none

private def effectValidationStep (caps : Capabilities) (decls : List StateDecl)
    (span : SourceSpan) (effect : Effect) (env : TypeEnv) :
    Except Diagnostic (ForInStep TypeEnv) :=
  match effectCheck caps decls env effect with
  | .error message => .error {span, message}
  | .ok none => .ok (.yield env)
  | .ok (some (name, ty)) =>
    if (env.lookup name).isSome then
      .error {span, message := s!"state read shadows '{name}'"}
    else .ok (.yield (env ++ [(name, ty)]))

inductive EffectValidation (state : List StateDecl) :
    TypeEnv → Effect → TypeEnv → Prop where
  | readCell {env : TypeEnv} {stateName destination : String} {ty : Ty}
      (declared : HasDeclaration state stateName (.cell ty))
      (fresh : env.lookup destination = none) :
      EffectValidation state env (.readCell stateName destination ty)
        (env ++ [(destination, ty)])
  | readMap {env : TypeEnv} {stateName destination : String}
      {keyTy valueTy : Ty} {key : Expr keyTy}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ())
      (fresh : env.lookup destination = none) :
      EffectValidation state env
        (.readMap stateName destination keyTy valueTy key)
        (env ++ [(destination, valueTy)])
  | require {env : TypeEnv} {condition : Expr .bool}
      (conditionValid : condition.validate stateEffectCaps env = .ok ()) :
      EffectValidation state env (.require condition) env
  | writeCell {env : TypeEnv} {stateName : String} {ty : Ty}
      {value : Expr ty} (declared : HasDeclaration state stateName (.cell ty))
      (valueValid : value.validate stateEffectCaps env = .ok ()) :
      EffectValidation state env (.writeCell stateName ty value) env
  | writeMap {env : TypeEnv} {stateName : String} {keyTy valueTy : Ty}
      {key : Expr keyTy} {value : Expr valueTy}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ())
      (valueValid : value.validate stateEffectCaps env = .ok ()) :
      EffectValidation state env (.writeMap stateName keyTy valueTy key value) env
  | requireAbsent {env : TypeEnv} {stateName : String} {keyTy : Ty}
      {key : Expr keyTy} {valueTy : Ty}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ()) :
      EffectValidation state env (.requireAbsent stateName keyTy key) env

inductive ValidatedEffects (state : List StateDecl) :
    TypeEnv → List Effect → TypeEnv → Prop where
  | nil {env : TypeEnv} : ValidatedEffects state env [] env
  | readCell {env final : TypeEnv} {rest : List Effect}
      {stateName destination : String} {ty : Ty}
      (declared : HasDeclaration state stateName (.cell ty))
      (fresh : env.lookup destination = none)
      (tail : ValidatedEffects state (env ++ [(destination, ty)]) rest final) :
      ValidatedEffects state env (.readCell stateName destination ty :: rest) final
  | readMap {env final : TypeEnv} {rest : List Effect}
      {stateName destination : String} {keyTy valueTy : Ty}
      {key : Expr keyTy}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ())
      (fresh : env.lookup destination = none)
      (tail : ValidatedEffects state (env ++ [(destination, valueTy)]) rest final) :
      ValidatedEffects state env
        (.readMap stateName destination keyTy valueTy key :: rest) final
  | require {env final : TypeEnv} {rest : List Effect}
      {condition : Expr .bool}
      (conditionValid : condition.validate stateEffectCaps env = .ok ())
      (tail : ValidatedEffects state env rest final) :
      ValidatedEffects state env (.require condition :: rest) final
  | writeCell {env final : TypeEnv} {rest : List Effect}
      {stateName : String} {ty : Ty} {value : Expr ty}
      (declared : HasDeclaration state stateName (.cell ty))
      (valueValid : value.validate stateEffectCaps env = .ok ())
      (tail : ValidatedEffects state env rest final) :
      ValidatedEffects state env (.writeCell stateName ty value :: rest) final
  | writeMap {env final : TypeEnv} {rest : List Effect}
      {stateName : String} {keyTy valueTy : Ty}
      {key : Expr keyTy} {value : Expr valueTy}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ())
      (valueValid : value.validate stateEffectCaps env = .ok ())
      (tail : ValidatedEffects state env rest final) :
      ValidatedEffects state env (.writeMap stateName keyTy valueTy key value :: rest) final
  | requireAbsent {env final : TypeEnv} {rest : List Effect}
      {stateName : String} {keyTy valueTy : Ty} {key : Expr keyTy}
      (declared : HasDeclaration state stateName (.map keyTy valueTy))
      (keyValid : key.validate stateEffectCaps env = .ok ())
      (tail : ValidatedEffects state env rest final) :
      ValidatedEffects state env (.requireAbsent stateName keyTy key :: rest) final

theorem ValidatedEffects.uncons {state : List StateDecl} {types final : TypeEnv}
    {effect : Effect} {rest : List Effect}
    (chain : ValidatedEffects state types (effect :: rest) final) :
    ∃ nextTypes, EffectValidation state types effect nextTypes ∧
      ValidatedEffects state nextTypes rest final := by
  cases chain with
  | readCell declared fresh tail =>
    exact ⟨_, .readCell declared fresh, tail⟩
  | readMap declared keyValid fresh tail =>
    exact ⟨_, .readMap declared keyValid fresh, tail⟩
  | require conditionValid tail => exact ⟨_, .require conditionValid, tail⟩
  | writeCell declared valueValid tail =>
    exact ⟨_, .writeCell declared valueValid, tail⟩
  | writeMap declared keyValid valueValid tail =>
    exact ⟨_, .writeMap declared keyValid valueValid, tail⟩
  | requireAbsent declared keyValid tail =>
    exact ⟨_, .requireAbsent declared keyValid, tail⟩

private theorem effectValidationStep_shape (caps : Capabilities)
    (decls : List StateDecl) (span : SourceSpan) (effect : Effect)
    (env : TypeEnv) (step : ForInStep TypeEnv)
    (success : effectValidationStep caps decls span effect env = .ok step) :
    ∃ result, effectCheck caps decls env effect = .ok result ∧
      step = .yield (env ++ result.toList) ∧
      ∀ pair ∈ result.toList, env.lookup pair.1 = none := by
  cases checked : effectCheck caps decls env effect with
  | error message => simp [effectValidationStep, checked] at success
  | ok result =>
    cases result with
    | none =>
      simp only [effectValidationStep, checked] at success
      refine ⟨none, rfl, ?_, by simp⟩
      simpa using (Except.ok.inj success).symm
    | some pair =>
      rcases pair with ⟨name, ty⟩
      by_cases shadow : (env.lookup name).isSome
      · simp [effectValidationStep, checked, shadow] at success
      · have stepShape : step = .yield (env ++ [(name, ty)]) := by
          simp only [effectValidationStep, checked] at success
          split at success
          · simp at success
          · exact (Except.ok.inj success).symm
        have freshName : env.lookup name = none := by
          cases lookup : env.lookup name with
          | none => rfl
          | some value => simp [lookup] at shadow
        refine ⟨some (name, ty), rfl, stepShape, ?_⟩
        intro found member
        simp only [Option.toList_some, List.mem_singleton] at member
        cases member
        simpa using freshName

private theorem effectStep_validated (decls : List StateDecl) (span : SourceSpan)
    (effect : Effect) (env : TypeEnv) (step : ForInStep TypeEnv)
    (success : effectValidationStep stateEffectCaps decls span effect env = .ok step) :
    ∃ after, step = .yield after ∧ EffectValidation decls env effect after := by
  obtain ⟨result, checked, shape, fresh⟩ :=
    effectValidationStep_shape stateEffectCaps decls span effect env step success
  cases effect with
  | readCell stateName destination ty =>
    change (requireDeclaredState decls stateName (.cell ty) >>= fun _ =>
      .ok (some (destination, ty))) = .ok result at checked
    rcases bind_ok.mp checked with ⟨_, declarationValid, resultValid⟩
    have declaration : HasDeclaration decls stateName (.cell ty) := by
      unfold requireDeclaredState at declarationValid
      cases found : decls.find? (fun item => item.name == stateName) with
      | none => simp [found] at declarationValid
      | some item =>
        cases matching : item.kind == .cell ty with
        | false => simp [found, matching] at declarationValid
        | true =>
          have kindEqual := kind_cell_beq_true item.kind ty matching
          exact ⟨item, found, kindEqual⟩
    have resultEq : result = some (destination, ty) := by
      exact (Except.ok.inj resultValid).symm
    subst result
    refine ⟨env ++ [(destination, ty)], shape, ?_⟩
    exact .readCell declaration (fresh (destination, ty) (by simp))
  | readMap stateName destination keyTy valueTy key =>
    change (requireDeclaredState decls stateName (.map keyTy valueTy) >>= fun _ =>
      key.validate stateEffectCaps env >>= fun _ =>
        .ok (some (destination, valueTy))) = .ok result at checked
    rcases bind_ok.mp checked with ⟨_, declarationValid, restValid⟩
    rcases bind_ok.mp restValid with ⟨_, keyValid, resultValid⟩
    have declaration : HasDeclaration decls stateName (.map keyTy valueTy) := by
      unfold requireDeclaredState at declarationValid
      cases found : decls.find? (fun item => item.name == stateName) with
      | none => simp [found] at declarationValid
      | some item =>
        cases matching : item.kind == .map keyTy valueTy with
        | false => simp [found, matching] at declarationValid
        | true => exact ⟨item, found, kind_map_beq_true item.kind keyTy valueTy matching⟩
    have resultEq : result = some (destination, valueTy) :=
      (Except.ok.inj resultValid).symm
    subst result
    refine ⟨env ++ [(destination, valueTy)], shape, ?_⟩
    exact .readMap declaration keyValid (fresh (destination, valueTy) (by simp))
  | require condition =>
    change (condition.validate stateEffectCaps env >>= fun _ => .ok none) =
      .ok result at checked
    rcases bind_ok.mp checked with ⟨_, conditionValid, resultValid⟩
    have resultEq : result = none := (Except.ok.inj resultValid).symm
    subst result
    exact ⟨env, by simpa using shape, .require conditionValid⟩
  | writeCell stateName ty value =>
    change (requireDeclaredState decls stateName (.cell ty) >>= fun _ =>
      value.validate stateEffectCaps env >>= fun _ => .ok none) = .ok result at checked
    rcases bind_ok.mp checked with ⟨_, declarationValid, restValid⟩
    rcases bind_ok.mp restValid with ⟨_, valueValid, resultValid⟩
    have declaration : HasDeclaration decls stateName (.cell ty) := by
      unfold requireDeclaredState at declarationValid
      cases found : decls.find? (fun item => item.name == stateName) with
      | none => simp [found] at declarationValid
      | some item =>
        cases matching : item.kind == .cell ty with
        | false => simp [found, matching] at declarationValid
        | true => exact ⟨item, found, kind_cell_beq_true item.kind ty matching⟩
    have resultEq : result = none := (Except.ok.inj resultValid).symm
    subst result
    exact ⟨env, by simpa using shape, .writeCell declaration valueValid⟩
  | writeMap stateName keyTy valueTy key value =>
    change (requireDeclaredState decls stateName (.map keyTy valueTy) >>= fun _ =>
      key.validate stateEffectCaps env >>= fun _ =>
        value.validate stateEffectCaps env >>= fun _ => .ok none) = .ok result at checked
    rcases bind_ok.mp checked with ⟨_, declarationValid, restValid⟩
    rcases bind_ok.mp restValid with ⟨_, keyValid, restValid⟩
    rcases bind_ok.mp restValid with ⟨_, valueValid, resultValid⟩
    have declaration : HasDeclaration decls stateName (.map keyTy valueTy) := by
      unfold requireDeclaredState at declarationValid
      cases found : decls.find? (fun item => item.name == stateName) with
      | none => simp [found] at declarationValid
      | some item =>
        cases matching : item.kind == .map keyTy valueTy with
        | false => simp [found, matching] at declarationValid
        | true => exact ⟨item, found, kind_map_beq_true item.kind keyTy valueTy matching⟩
    have resultEq : result = none := (Except.ok.inj resultValid).symm
    subst result
    exact ⟨env, by simpa using shape, .writeMap declaration keyValid valueValid⟩
  | requireAbsent stateName keyTy key =>
    -- This branch mirrors the source validator's special map-kind and key-type check.
    cases found : decls.find? (fun item => item.name == stateName) with
    | none => simp [effectCheck, stateEffectCaps, found, throw, throwThe,
        bind, Except.bind] at checked
    | some item =>
      cases item with
      | mk itemName kind itemSpan =>
        cases kind with
        | cell cellTy =>
          simp [effectCheck, stateEffectCaps, found, throw, throwThe,
            bind, Except.bind] at checked
        | map foundKey foundValue =>
          by_cases keySame : foundKey = keyTy
          · have equalTy : (foundKey == keyTy) = true := by
              subst foundKey
              cases keyTy <;> simp [BEq.beq, instBEqTy.beq]
            have mismatch : (foundKey != keyTy) = false := by simp [bne, equalTy]
            have keyValid : key.validate stateEffectCaps env = .ok () := by
              cases keyChecked : key.validate stateEffectCaps env with
              | error message =>
                simp [effectCheck, stateEffectCaps, found, mismatch] at checked
                dsimp [stateEffectCaps] at keyChecked
                rw [keyChecked] at checked
                cases checked
              | ok value =>
                cases value
                simp
            have resultEq : result = none := by
              have checked' := checked
              simp [effectCheck, stateEffectCaps, found, mismatch] at checked'
              have keyValid' := keyValid
              dsimp [stateEffectCaps] at keyValid'
              rw [keyValid'] at checked'
              exact (Except.ok.inj checked').symm
            subst result
            refine ⟨env, by simpa using shape,
              .requireAbsent (valueTy := foundValue) ?_ keyValid⟩
            refine ⟨{name := itemName, kind := .map foundKey foundValue, span := itemSpan}, ?_, ?_⟩
            · simpa using found
            · simp [keySame]
          · have unequalTy : (foundKey == keyTy) = false := by
              cases equal : (foundKey == keyTy) with
              | false => rfl
              | true =>
                have typeEqual := type_beq_true foundKey keyTy equal
                exact False.elim (keySame typeEqual)
            have mismatch : (foundKey != keyTy) = true := by simp [bne, unequalTy]
            simp [effectCheck, stateEffectCaps, found, mismatch, throw, throwThe,
              bind, Except.bind] at checked

private theorem forIn_append_shape
    (body : α → TypeEnv → Except ε (ForInStep TypeEnv))
    (binding : α → String × Ty) (values : List α)
    (before after : TypeEnv)
    (actions : ∀ value env step, body value env = .ok step →
      step = .yield (env ++ [binding value]))
    (success : forIn values before body = .ok after) :
    after = before ++ values.map binding := by
  induction values generalizing before with
  | nil =>
    change Except.ok before = .ok after at success
    cases success
    simp
  | cons value rest ih =>
    rw [List.forIn_cons] at success
    cases checked : body value before with
    | error message => simp [checked, bind, Except.bind] at success
    | ok step =>
      have equal := actions value before step checked
      subst step
      simp only [checked, bind, Except.bind] at success
      simpa [List.append_assoc] using ih _ success

private theorem forIn_validated_effects (state : List StateDecl)
    (span : SourceSpan) (effects : List Effect) (initial final : TypeEnv)
    (success : forIn effects initial
      (fun effect env => effectValidationStep stateEffectCaps state span effect env) =
        .ok final) :
    ValidatedEffects state initial effects final := by
  induction effects generalizing initial with
  | nil =>
    change Except.ok initial = .ok final at success
    cases success
    exact .nil
  | cons effect rest ih =>
    rw [List.forIn_cons] at success
    cases checked : effectValidationStep stateEffectCaps state span effect initial with
    | error message => simp [checked, bind, Except.bind] at success
    | ok step =>
      obtain ⟨middle, shape, validated⟩ :=
        effectStep_validated state span effect initial step checked
      simp only [checked, bind, Except.bind] at success
      rw [shape] at success
      have tail := ih middle success
      cases validated with
      | readCell declared fresh => exact .readCell declared fresh tail
      | readMap declared keyValid fresh => exact .readMap declared keyValid fresh tail
      | require conditionValid => exact .require conditionValid tail
      | writeCell declared valueValid => exact .writeCell declared valueValid tail
      | writeMap declared keyValid valueValid => exact .writeMap declared keyValid valueValid tail
      | requireAbsent declared keyValid => exact .requireAbsent declared keyValid tail

def initialEffectTypeEnv (ep : Entrypoint) : TypeEnv :=
  ep.circuit.inputs.map (fun input => (input.name, input.ty)) ++
    ep.circuit.outputs.map (fun output => (output.name, output.ty))

/-- Accepted production lowering inherits a typed and fresh effect chain from
the actual source entrypoint validator. Read steps append their binding, and
all later expressions validate against that exact prefix environment. -/
theorem lower_validated_effects (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    ∃ final, ValidatedEffects state (initialEffectTypeEnv ep) ep.effects final := by
  have source := GenericStateAdmission.lower_source_validated state ep plan accepted
  unfold Entrypoint.validate at source
  simp only [bind_ok] at source
  obtain ⟨_, _, _, _, env, outputsChecked, final, effectsChecked, _⟩ := source
  have outputShape : env = initialEffectTypeEnv ep := by
    have shape := forIn_append_shape _
      (fun output : Output => (output.name, output.ty)) ep.circuit.outputs
      (ep.circuit.inputs.map (fun input => (input.name, input.ty))) env
      (by
        intro output before step success
        split at success
        · simp [throw, throwThe, bind, Except.bind] at success
        · change Except.ok (.yield (before ++ [(output.name, output.ty)])) =
            .ok step at success
          exact (Except.ok.inj success).symm)
      outputsChecked
    simpa [initialEffectTypeEnv, List.map_append, List.map_map,
      Function.comp_def] using shape
  have checkedEffects : forIn ep.effects env
      (fun effect current => effectValidationStep stateEffectCaps state ep.span effect current) =
        .ok final := by
    change forIn ep.effects env
      (fun effect current => effectValidationStep stateEffectCaps state ep.span effect current) =
        .ok final
    exact effectsChecked
  subst env
  exact ⟨final, forIn_validated_effects state ep.span ep.effects
    (initialEffectTypeEnv ep) final checkedEffects⟩

#print axioms lower_validated_effects

end Noctium.Verification.GenericStateEffectValidation
