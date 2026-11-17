import Nightlean.Verification.GenericStateReadTypes

namespace Nightlean.Verification.GenericStateReadNames
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem lookup_none_fresh (env : TypeEnv) (name : String)
    (absent : env.lookup name = none) : name ∉ env.map Prod.fst := by
  intro member
  obtain ⟨pair, present, same⟩ := List.mem_map.mp member
  have different := List.lookup_eq_none_iff.mp absent pair present
  simp [same] at different

private theorem forIn_bindings_fresh
    (body : α → TypeEnv → Except ε (ForInStep TypeEnv))
    (binding : α → Option (String × Ty)) (values : List α)
    (before after : TypeEnv)
    (actions : ∀ value env step, body value env = .ok step →
      step = .yield (env ++ (binding value).toList) ∧
      ∀ pair ∈ (binding value).toList, env.lookup pair.1 = none)
    (success : forIn values before body = .ok after) :
    after = before ++ values.filterMap binding ∧
      ((values.filterMap binding).map Prod.fst).Nodup ∧
      ∀ name ∈ (values.filterMap binding).map Prod.fst,
        name ∉ before.map Prod.fst := by
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
      obtain ⟨equal, fresh⟩ := actions value before step checked
      subst step
      simp only [checked, bind, Except.bind] at success
      obtain ⟨final, distinct, unused⟩ := ih _ success
      cases found : binding value with
      | none =>
        simpa only [List.filterMap_cons, found, Option.toList_none,
          List.append_nil] using And.intro final (And.intro distinct unused)
      | some pair =>
        have absent := fresh pair (by simp [found])
        have headFresh := lookup_none_fresh before pair.1 absent
        have notInRest : pair.1 ∉ (rest.filterMap binding).map Prod.fst := by
          intro member
          exact unused pair.1 member (by simp [found])
        constructor
        · simpa [found, List.append_assoc] using final
        constructor
        · simpa [found] using List.nodup_cons.mpr ⟨notInRest, distinct⟩
        · intro name member
          simp only [List.filterMap_cons, found, List.map_cons, List.mem_cons] at member
          rcases member with equal | present
          · simpa [equal] using headFresh
          · intro old
            exact unused name present (by simp [found, old])

private def readBinding : Effect → Option (String × Ty)
  | .readCell _ destination ty => some (destination, ty)
  | .readMap _ destination _ ty _ => some (destination, ty)
  | _ => none

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

private theorem validationStep_success (span : SourceSpan) (env : TypeEnv)
    (checked : Except String (Option (String × Ty))) (step : ForInStep TypeEnv)
    (success : validationStep span env checked = .ok step) :
    ∃ result, checked = .ok result ∧
      step = .yield (env ++ result.toList) ∧
      ∀ pair ∈ result.toList, env.lookup pair.1 = none := by
  cases checked with
  | error message => simp [validationStep, throw, throwThe, bind, Except.bind] at success
  | ok result =>
    refine ⟨result, rfl, ?_⟩
    cases result with
    | none =>
      change Except.ok (.yield env) = .ok step at success
      exact ⟨by simpa using (Except.ok.inj success).symm, by simp⟩
    | some pair =>
      rcases pair with ⟨name, ty⟩
      simp only [validationStep] at success
      split at success
      next shadow => simp [throw, throwThe, bind, Except.bind] at success
      next clear =>
        change Except.ok (.yield (env ++ [(name, ty)])) = .ok step at success
        refine ⟨(Except.ok.inj success).symm, ?_⟩
        cases lookup : env.lookup name with
        | none =>
          intro pair member
          simp only [Option.toList_some, List.mem_singleton] at member
          cases member
          exact lookup
        | some found => simp [lookup] at clear

private theorem forIn_checked_fresh
    (span : SourceSpan) (checks : α → TypeEnv → Except String (Option (String × Ty)))
    (binding : α → Option (String × Ty)) (values : List α)
    (before after : TypeEnv)
    (shape : ∀ value env result, checks value env = .ok result → result = binding value)
    (success : forIn values before
      (fun value env => validationStep span env (checks value env)) = .ok after) :
    after = before ++ values.filterMap binding ∧
      ((values.filterMap binding).map Prod.fst).Nodup ∧
      ∀ name ∈ (values.filterMap binding).map Prod.fst,
        name ∉ before.map Prod.fst := by
  refine forIn_bindings_fresh _ binding values before after ?_ success
  intro value env step accepted
  obtain ⟨result, checked, equal, unused⟩ :=
    validationStep_success span env (checks value env) step accepted
  rw [shape value env result checked] at equal unused
  exact ⟨equal, unused⟩

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

/-- Ordered destinations introduced by source state-read effects. -/
def sourceReadNames (effects : List Effect) : List String :=
  (effects.filterMap readBinding).map Prod.fst

/-- The actual source validator rejects duplicate read destinations and reads
which shadow any original circuit input or computed output binding. -/
theorem lower_source_read_names (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    (sourceReadNames ep.effects).Nodup ∧
      ∀ name ∈ sourceReadNames ep.effects,
        name ∉ ep.circuit.inputs.map (·.name) ++ ep.circuit.outputs.map (·.name) := by
  have source := GenericStateAdmission.lower_source_validated state ep plan accepted
  unfold Entrypoint.validate at source
  simp only [bind_ok] at source
  obtain ⟨_, _, _, _, env, outputsChecked, final, effectsChecked, _⟩ := source
  have fresh := forIn_checked_fresh ep.span _ readBinding ep.effects env final
    (by
      intro effect before result success
      cases effect with
      | readCell name destination ty =>
        dsimp at success
        simp only [bind_ok] at success
        obtain ⟨_, _, equal⟩ := success
        exact (Except.ok.inj equal).symm
      | readMap name destination keyTy valueTy key =>
        dsimp at success
        simp only [bind_ok] at success
        obtain ⟨_, _, _, _, equal⟩ := success
        exact (Except.ok.inj equal).symm
      | require condition =>
        dsimp at success
        simp only [bind_ok] at success
        obtain ⟨_, _, equal⟩ := success
        exact (Except.ok.inj equal).symm
      | writeCell name ty value =>
        dsimp at success
        simp only [bind_ok] at success
        obtain ⟨_, _, _, _, equal⟩ := success
        exact (Except.ok.inj equal).symm
      | writeMap name keyTy valueTy key value =>
        dsimp at success
        simp only [bind_ok] at success
        obtain ⟨_, _, _, _, _, _, equal⟩ := success
        exact (Except.ok.inj equal).symm
      | requireAbsent name keyTy key =>
        dsimp at success
        split at success
        · split at success
          · simp [throw, throwThe, bind, Except.bind] at success
          · simp only [bind_ok] at success
            obtain ⟨_, _, equal⟩ := success
            exact (Except.ok.inj equal).symm
        · simp [throw, throwThe, bind, Except.bind] at success)
    effectsChecked
  have outputEnv := forIn_append_shape _
    (fun output : Output => (output.name, output.ty)) ep.circuit.outputs
    (ep.circuit.inputs.map (fun input => (input.name, input.ty))) env
    (by
      intro output before step success
      split at success
      · simp [throw, throwThe, bind, Except.bind] at success
      · change Except.ok (.yield (before ++ [(output.name, output.ty)])) = .ok step at success
        exact (Except.ok.inj success).symm)
    outputsChecked
  refine ⟨fresh.2.1, ?_⟩
  intro name member
  have unused := fresh.2.2 name member
  simpa only [outputEnv, List.map_append, List.map_map, Function.comp_def] using unused

end Nightlean.Verification.GenericStateReadNames
