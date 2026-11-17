import Nightlean.Semantics

namespace Nightlean.Verification.SourceEffects

abbrev Frame := EvalEnv × LedgerState

def canonicalValue (ctx : EvalContext) (ty : Ty) (value : ty.Denote) : Bool :=
  match ty with
  | .native => value < ctx.modulus
  | .bool => true
  | .uint maximum => maximum ≤ ScalarPolicy.maxUint && value ≤ maximum && value < ctx.modulus

def updateEntry [BEq α] (key : α) (value : β) (entries : List (α × β)) : List (α × β) :=
  (key, value) :: entries.filter (fun item => !(item.1 == key))

private theorem bind_ok {α β : Type} (value : α) (next : α → Except String β) :
    ((Except.ok value : Except String α) >>= next) = next value := rfl
private theorem bind_error {α β : Type} (message : String) (next : α → Except String β) :
    ((Except.error message : Except String α) >>= next) = .error message := rfl
private theorem map_ok {α β : Type} (f : α → β) (value : α) :
    f <$> (Except.ok value : Except String α) = Except.ok (f value) := rfl
private theorem map_error {α β : Type} (f : α → β) (message : String) :
    f <$> (Except.error message : Except String α) = Except.error message := rfl
private theorem throw_error {α : Type} (message : String) :
    (throw message : Except String α) = .error message := rfl
private theorem pure_ok {α : Type} (value : α) :
    (pure value : Except String α) = .ok value := rfl

attribute [local simp] bind_ok bind_error map_ok map_error throw_error pure_ok

/-- One ordered source effect, including the environment produced by reads. -/
def step (ctx : EvalContext) (effect : Effect) (frame : Frame) : Except String Frame := do
  let mut env := frame.1
  let mut next := frame.2
  match effect with
  | .readCell name destination ty =>
    let some raw := next.cells.lookup name | throw s!"missing state cell '{name}'"
    let some value := raw.as ty | throw s!"state cell type mismatch '{name}'"
    if !canonicalValue ctx ty value then throw s!"noncanonical state cell '{name}'"
    env := (destination, Value.pack ty value) :: env
  | .readMap name destination keyTy valueTy key =>
    let key := Value.pack keyTy (← key.eval ctx env)
    let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
    let some raw := entries.lookup key | throw s!"missing map key in '{name}'"
    let some value := raw.as valueTy | throw s!"state map value type mismatch '{name}'"
    if !canonicalValue ctx valueTy value then throw s!"noncanonical state map value '{name}'"
    env := (destination, Value.pack valueTy value) :: env
  | .require condition =>
    if !(← condition.eval ctx env) then throw "state transition guard failed"
  | .writeCell name ty value =>
    let some existing := next.cells.lookup name | throw s!"missing state cell '{name}'"
    if (existing.as ty).isNone then throw s!"state cell type mismatch '{name}'"
    next := {next with cells := updateEntry name (Value.pack ty (← value.eval ctx env)) next.cells}
  | .writeMap name keyTy valueTy key value =>
    let key := Value.pack keyTy (← key.eval ctx env)
    let value := Value.pack valueTy (← value.eval ctx env)
    let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
    for (oldKey, oldValue) in entries do
      if (oldKey.as keyTy).isNone || (oldValue.as valueTy).isNone then
        throw s!"state map type mismatch '{name}'"
    next := {next with maps := updateEntry name (updateEntry key value entries) next.maps}
  | .requireAbsent name keyTy key =>
    let key := Value.pack keyTy (← key.eval ctx env)
    let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
    if (entries.lookup key).isSome then throw "state map key already present"
  pure (env, next)


def fold (ctx : EvalContext) (effects : List Effect) (frame : Frame) : Except String Frame :=
  effects.foldlM (fun frame effect => step ctx effect frame) frame

@[simp] theorem fold_nil (ctx : EvalContext) (frame : Frame) :
    fold ctx [] frame = .ok frame := rfl

theorem fold_cons (ctx : EvalContext) (effect : Effect) (rest : List Effect) (frame : Frame) :
    fold ctx (effect :: rest) frame = (step ctx effect frame).bind (fold ctx rest) := rfl

theorem fold_append (ctx : EvalContext) (before after : List Effect) (frame : Frame) :
    fold ctx (before ++ after) frame = (fold ctx before frame).bind (fold ctx after) := by
  exact List.foldlM_append

/-- Exact equality with the unchanged evaluator, including every error branch. -/
theorem runEffects_eq_fold (ctx : EvalContext) (effects : List Effect)
    (env : EvalEnv) (state : LedgerState) :
    runEffects ctx effects env state = (fold ctx effects (env, state)).map Prod.snd := by
  have hf : (forIn effects (env, state) fun effect frame =>
      ForInStep.yield <$> step ctx effect frame) =
      effects.foldlM (fun frame effect => step ctx effect frame) (env, state) := by
    simp
  unfold runEffects fold
  rw [← hf]
  simp only [map_eq_pure_bind]
  congr 1
  congr 1
  funext effect frame
  cases effect with
  | readCell name destination ty =>
    cases hl : frame.2.cells.lookup name with
    | none => simp [step, hl]
    | some raw =>
      cases hv : raw.as ty with
      | none => simp [step, hl, hv]
      | some value =>
        cases hc : canonicalValue ctx ty value <;>
          simp_all [step, canonicalValue, canonical_eq]
        all_goals exact hc
  | readMap name destination keyTy valueTy key =>
    cases hk : key.eval ctx frame.1 with
    | error message => simp [step, hk]
    | ok keyValue =>
      cases hl : frame.2.maps.lookup name with
      | none => simp [step, hk, hl]
      | some entries =>
        cases he : entries.lookup (Value.pack keyTy keyValue) with
        | none => simp [step, hk, hl, he]
        | some raw =>
          cases hv : raw.as valueTy with
          | none => simp [step, hk, hl, he, hv]
          | some value =>
            cases hc : canonicalValue ctx valueTy value <;>
              simp_all [step, canonicalValue, canonical_eq]
            all_goals exact hc
  | require condition =>
    cases he : condition.eval ctx frame.1 with
    | error message => simp [step, he]
    | ok value => cases value <;> simp [step, he]
  | writeCell name ty value =>
    cases hl : frame.2.cells.lookup name with
    | none => simp [step, hl]
    | some raw =>
      cases hv : (raw.as ty).isNone <;>
        simp [step, hl, hv, updateEntry]
      all_goals rfl
  | writeMap name keyTy valueTy key value =>
    cases hk : key.eval ctx frame.1 with
    | error message => simp [step, hk]
    | ok keyValue =>
      cases hv : value.eval ctx frame.1 with
      | error message => simp [step, hk, hv]
      | ok result =>
        cases hl : frame.2.maps.lookup name with
        | none => simp [step, hk, hv, hl]
        | some entries =>
          simp [step, hk, hv, hl, updateEntry]
          rfl
  | requireAbsent name keyTy key =>
    cases hk : key.eval ctx frame.1 with
    | error message => simp [step, hk]
    | ok keyValue =>
      cases hl : frame.2.maps.lookup name with
      | none => simp [step, hk, hl]
      | some entries =>
        cases he : (entries.lookup (Value.pack keyTy keyValue)).isSome <;>
          simp [step, hk, hl, he]


theorem runEffects_ok_iff (ctx : EvalContext) (effects : List Effect)
    (env : EvalEnv) (state next : LedgerState) :
    runEffects ctx effects env state = .ok next ↔
      ∃ finalEnv, fold ctx effects (env, state) = .ok (finalEnv, next) := by
  rw [runEffects_eq_fold]
  cases result : fold ctx effects (env, state) with
  | error message => simp [Except.map]
  | ok frame => cases frame; simp [Except.map]

end Nightlean.Verification.SourceEffects
