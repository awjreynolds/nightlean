import Noctium.Verification.GenericStateReadTape

namespace Noctium.Verification.GenericStateGuardTape
open Backend

/-- The actual source effect's guard contribution at the live read count. -/
def effectGuardChunk (effect : Effect) (ordinal : Nat) : List (Expr .bool) :=
  match effect with
  | .require condition => [condition]
  | .requireAbsent .. =>
    [.eq (.ref (GenericStateNativeReadNames.absenceName ordinal) : Expr .bool)
      (.bool false)]
  | _ => []

def guardChunks : List Effect → Nat → List (List (Expr .bool))
  | [], _ => []
  | effect :: rest, ordinal =>
    effectGuardChunk effect ordinal ::
      guardChunks rest (ordinal + (GenericStateReadTape.effectReadChunk effect ordinal).length)

theorem appendEffect_guard_chunk (state : List StateDecl) (effect : Effect)
    (before after : Impact.Plan)
    (accepted : Impact.appendEffect state effect before = .ok after) :
    after.guards = before.guards ++ effectGuardChunk effect before.reads.length := by
  have same :
      Impact.Plan.guards <$> Impact.appendEffect state effect before =
      (fun _ => before.guards ++ effectGuardChunk effect before.reads.length) <$>
        Impact.appendEffect state effect before := by
    cases effect <;>
      simp only [Impact.appendEffect, effectGuardChunk,
        GenericStateNativeReadNames.absenceName, map_bind,
        LawfulApplicative.map_pure, List.append_nil] <;> rfl
  rw [accepted] at same
  exact Except.ok.inj same

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

theorem appendEffects_guard_chunks (state : List StateDecl)
    (effects : List Effect) (before after : Impact.Plan)
    (accepted : Impact.appendEffects state effects before = .ok after) :
    after.guards = before.guards ++
      (guardChunks effects before.reads.length).flatten := by
  induction effects generalizing before with
  | nil =>
    change Except.ok before = .ok after at accepted
    cases accepted
    simp [guardChunks]
  | cons effect rest ih =>
    simp only [Impact.appendEffects, List.foldlM_cons, bind_ok] at accepted
    obtain ⟨middle, first, later⟩ := accepted
    have guards := appendEffect_guard_chunk state effect before middle first
    have reads := GenericStateReadTape.appendEffect_read_chunk
      state effect before middle first
    rw [ih middle later, guards, reads]
    simp [guardChunks, List.length_append, List.append_assoc]

private theorem publicInputPlan_guards (inputs : List Input)
    (initial : Impact.Plan) :
    (Impact.publicInputPlan inputs initial).guards = initial.guards := by
  induction inputs generalizing initial with
  | nil => rfl
  | cons input rest ih =>
    change (Impact.publicInputPlan rest
      (Impact.publicInputPlan [input] initial)).guards = initial.guards
    rw [ih]
    cases input with
    | mk name ty visibility span => cases visibility <;> rfl

/-- Guard expressions in the accepted plan occur in source effect order,
with generated absence guards using exact live read-count names. -/
theorem lower_guard_chunks (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (accepted : Impact.lower state ep = .ok plan) :
    plan.guards = (guardChunks ep.effects
      ((ep.circuit.inputs.filter (·.visibility == .«public»)).length)).flatten := by
  let initial := Impact.publicInputPlan ep.circuit.inputs {}
  have prefixLength : initial.reads.length =
      (ep.circuit.inputs.filter (·.visibility == .«public»)).length := by
    simp only [initial, GenericStateNativeReadNames.publicInputPlan_reads,
      List.nil_append, List.length_map]
  have shape := appendEffects_guard_chunks state ep.effects initial plan
    (GenericStateAdmission.lower_effect_fold state ep plan accepted)
  rw [shape, ← prefixLength]
  simp [initial, publicInputPlan_guards]

theorem require_guard_member (effects : List Effect) (ordinal : Nat)
    (condition : Expr .bool)
    (member : Effect.require condition ∈ effects) :
    condition ∈ (guardChunks effects ordinal).flatten := by
  induction effects generalizing ordinal with
  | nil => cases member
  | cons effect rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst effect
      simp [guardChunks, effectGuardChunk]
    · simp only [guardChunks, List.flatten_cons, List.mem_append]
      exact Or.inr (ih _ later)

theorem lower_require_guard_true (state : List StateDecl) (ep : Entrypoint)
    (plan : Impact.Plan) (ctx : EvalContext) (values : EvalEnv)
    (accepted : Impact.lower state ep = .ok plan)
    (truth : ∀ guard ∈ plan.guards, guard.eval ctx values = .ok true)
    (condition : Expr .bool) (member : Effect.require condition ∈ ep.effects) :
    condition.eval ctx values = .ok true := by
  apply truth condition
  rw [lower_guard_chunks state ep plan accepted]
  exact require_guard_member ep.effects _ condition member

end Noctium.Verification.GenericStateGuardTape
