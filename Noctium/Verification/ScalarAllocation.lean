import Noctium.Backend.Zkir

namespace Noctium.Verification.ScalarAllocation
open Backend

/-- Every allocated SSA name has an emitted defining instruction. -/
structure Frame (before after : Zkir.LowerState) : Prop where
  next : before.next ≤ after.next
  instructions : before.instructions.size + (after.next - before.next) ≤ after.instructions.size

theorem Frame.refl (state : Zkir.LowerState) : Frame state state := by
  constructor <;> simp

theorem Frame.trans {before middle after : Zkir.LowerState}
    (first : Frame before middle) (second : Frame middle after) : Frame before after := by
  rcases first with ⟨firstNext, firstSize⟩
  rcases second with ⟨secondNext, secondSize⟩
  constructor <;> omega

def PreservesFrame (operation : StateM Zkir.LowerState α) : Prop :=
  ∀ state, Frame state (operation.run state).2

theorem pure_preserves (value : α) : PreservesFrame (pure value) := by
  intro state
  exact Frame.refl state

theorem bind_preserves (first : StateM Zkir.LowerState α) (next : α → StateM Zkir.LowerState β)
    (firstFrame : PreservesFrame first) (nextFrame : ∀ value, PreservesFrame (next value)) :
    PreservesFrame (first >>= next) := by
  intro state
  change Frame state ((next (first.run state).1).run (first.run state).2).2
  exact (firstFrame state).trans (nextFrame _ _)

theorem get_preserves : PreservesFrame (get : StateM Zkir.LowerState Zkir.LowerState) := by
  exact Frame.refl

theorem modify_preserves (update : Zkir.LowerState → Zkir.LowerState)
    (preserves : ∀ state, Frame state (update state)) :
    PreservesFrame (modify update) := preserves

theorem emit_preserves (opcode : String) (fields : List (String × Lean.Json)) :
    PreservesFrame (Zkir.emit opcode fields) := by
  intro state
  change Frame state {state with instructions := state.instructions.push _}
  constructor
  · exact Nat.le_refl _
  · simp

theorem binary_preserves (opcode left right : String) :
    PreservesFrame (Zkir.binary opcode left right) := by
  intro state
  cases hit : state.expressions.lookup (opcode, [left, right], none) with
  | some result =>
    simp [Zkir.binary, StateT.run_bind, StateT.run_get, StateT.run_pure, hit]
    exact Frame.refl _
  | none =>
    simp [Zkir.binary, hit, Zkir.fresh, Zkir.emit, StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_modify, StateT.run_set]
    constructor
    · exact Nat.le_add_right _ _
    · change state.instructions.size + (state.next + 1 - state.next) ≤ (state.instructions.push _).size
      simp

theorem unary_preserves (opcode operand : String) :
    PreservesFrame (Zkir.unary opcode operand) := by
  intro state
  cases hit : state.expressions.lookup (opcode, [operand], none) with
  | some result =>
    simp [Zkir.unary, StateT.run_bind, StateT.run_get, StateT.run_pure, hit]
    exact Frame.refl _
  | none =>
    simp [Zkir.unary, hit, Zkir.fresh, Zkir.emit, StateT.run_bind, StateT.run_get, StateT.run_pure, StateT.run_modify, StateT.run_set]
    constructor
    · exact Nat.le_add_right _ _
    · change state.instructions.size + (state.next + 1 - state.next) ≤ (state.instructions.push _).size
      simp

theorem constrainUnsigned_preserves (maximum : Nat) (value : String) :
    PreservesFrame (Zkir.constrainUnsigned maximum value) := by
  intro state
  by_cases zero : maximum = 0
  · simp only [Zkir.constrainUnsigned, zero, beq_self_eq_true, ↓reduceIte]
    exact emit_preserves _ _ state
  · by_cases full : maximum + 1 = 2 ^ (maximum.log2 + 1)
    · simp [Zkir.constrainUnsigned, zero, full, Zkir.emit, StateT.run_bind, StateT.run_modify]
      constructor
      · exact Nat.le_refl _
      · change state.instructions.size + (state.next - state.next) ≤ (state.instructions.push _).size
        simp
    · simp [Zkir.constrainUnsigned, zero, full, Zkir.emit, Zkir.fresh, StateT.run_bind,
        StateT.run_get, StateT.run_modify, StateT.run_set]
      constructor
      · exact Nat.le_add_right _ _
      · change state.instructions.size + (state.next + 1 - state.next) ≤
          (((state.instructions.push _).push _).push _).size
        simp

theorem constrainType_preserves (ty : Ty) (value : String) :
    PreservesFrame (Zkir.constrainType ty value) := by
  cases ty with
  | native => exact pure_preserves ()
  | bool => exact emit_preserves _ _
  | uint maximum => exact constrainUnsigned_preserves maximum value

theorem bindPublic_preserves (values : List String) :
    PreservesFrame (Zkir.bindPublic values) := emit_preserves _ _

theorem aliases_preserves (aliases : List (String × String)) :
    PreservesFrame (modify fun state => {state with aliases := aliases}) := by
  intro state
  change Frame state {state with aliases := aliases}
  constructor <;> simp

theorem lowerExpr_preserves (expression : Expr ty) :
    PreservesFrame (Zkir.lowerExpr expression) := by
  induction expression with
  | native value => exact pure_preserves _
  | bool value => exact pure_preserves _
  | uint maximum value => exact pure_preserves _
  | ref name =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ get_preserves
    intro state
    exact pure_preserves _
  | add left right il ir =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ il
    intro left
    apply bind_preserves _ _ ir
    intro right
    exact binary_preserves _ _ _
  | mul left right il ir =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ il
    intro left
    apply bind_preserves _ _ ir
    intro right
    exact binary_preserves _ _ _
  | sub left right il ir =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ il
    intro left
    apply bind_preserves _ _ ir
    intro right
    apply bind_preserves _ _ (unary_preserves _ _)
    intro negated
    exact binary_preserves _ _ _
  | uadd left right il ir =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ il
    intro left
    apply bind_preserves _ _ ir
    intro right
    apply bind_preserves _ _ (binary_preserves _ _ _)
    intro output
    apply bind_preserves _ _ (constrainUnsigned_preserves _ _)
    intro unit
    exact pure_preserves _
  | umul left right il ir =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ il
    intro left
    apply bind_preserves _ _ ir
    intro right
    apply bind_preserves _ _ (binary_preserves _ _ _)
    intro output
    apply bind_preserves _ _ (constrainUnsigned_preserves _ _)
    intro unit
    exact pure_preserves _
  | usub left right il ir =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ il
    intro left
    apply bind_preserves _ _ ir
    intro right
    apply bind_preserves _ _ (unary_preserves _ _)
    intro negated
    apply bind_preserves _ _ (binary_preserves _ _ _)
    intro output
    apply bind_preserves _ _ (constrainUnsigned_preserves _ _)
    intro unit
    exact pure_preserves _
  | cast target value iv =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ iv
    intro output
    cases target with
    | native => exact pure_preserves _
    | bool =>
      apply bind_preserves _ _ (binary_preserves _ _ _)
      intro compared
      exact unary_preserves _ _
    | uint maximum =>
      apply bind_preserves _ _ (constrainUnsigned_preserves _ _)
      intro unit
      exact pure_preserves _
  | letE name value body iv ib =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ iv
    intro value
    apply bind_preserves _ _ get_preserves
    intro snapshot
    apply bind_preserves _ _ (aliases_preserves _)
    intro ignored
    apply bind_preserves _ _ ib
    intro result
    apply bind_preserves _ _ (aliases_preserves _)
    intro ignored
    exact pure_preserves _
  | assertE condition body ic ib =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ ic
    intro condition
    apply bind_preserves _ _ (emit_preserves _ _)
    intro unit
    exact ib
  | disclose span value iv => exact iv
  | eq left right il ir =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ il
    intro left
    apply bind_preserves _ _ ir
    intro right
    exact binary_preserves _ _ _
  | select condition yes no ic iy ino =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ ic
    intro condition
    apply bind_preserves _ _ iy
    intro yes
    apply bind_preserves _ _ ino
    intro no
    apply bind_preserves _ _ get_preserves
    intro snapshot
    cases hit : snapshot.expressions.lookup ("cond_select", [condition, yes, no], none) with
    | some result =>
      simp only [hit]
      exact pure_preserves _
    | none =>
      simp only [hit]
      intro state
      simp [Zkir.fresh, Zkir.emit, StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_set]
      constructor
      · exact Nat.le_add_right _ _
      · change state.instructions.size + (state.next + 1 - state.next) ≤ (state.instructions.push _).size
        simp
  | poseidon2 domain left right il ir =>
    simp only [Zkir.lowerExpr]
    apply bind_preserves _ _ il
    intro left
    apply bind_preserves _ _ ir
    intro right
    apply bind_preserves _ _ get_preserves
    intro snapshot
    cases hit : snapshot.expressions.lookup ("transient_hash", [left, right], some domain) with
    | some result =>
      simp only [hit]
      exact pure_preserves _
    | none =>
      simp only [hit]
      intro state
      simp [Zkir.fresh, Zkir.emit, StateT.run_bind, StateT.run_get, StateT.run_modify, StateT.run_set]
      constructor
      · exact Nat.le_add_right _ _
      · change state.instructions.size + (state.next + 1 - state.next) ≤ (state.instructions.push _).size
        simp

theorem lowerExpr_next (expression : Expr ty) (state : Zkir.LowerState) :
    state.next ≤ ((Zkir.lowerExpr expression).run state).2.next :=
  (lowerExpr_preserves expression state).next

theorem forIn_preserves (items : List α) (initial : β)
    (body : α → β → StateM Zkir.LowerState (ForInStep β))
    (preserves : ∀ item accumulator, PreservesFrame (body item accumulator)) :
    PreservesFrame (forIn items initial body) := by
  induction items generalizing initial with
  | nil => exact pure_preserves _
  | cons item rest ih =>
    rw [List.forIn_cons]
    apply bind_preserves _ _ (preserves item initial)
    intro step
    cases step with
    | done result => exact pure_preserves _
    | yield result => exact ih result

theorem lowerBody_preserves (circuit : Circuit) :
    PreservesFrame (Zkir.lowerBody circuit) := by
  unfold Zkir.lowerBody
  apply bind_preserves
  · apply forIn_preserves
    intro input accumulator
    apply bind_preserves _ _ (emit_preserves _ _)
    intro ignored
    apply bind_preserves _ _ (constrainType_preserves _ _)
    intro ignored
    split
    · apply bind_preserves _ _ (bindPublic_preserves _)
      intro ignored
      exact pure_preserves _
    · exact pure_preserves _
  · intro ignored
    apply bind_preserves
    · apply forIn_preserves
      intro condition accumulator
      apply bind_preserves _ _ (lowerExpr_preserves _)
      intro result
      apply bind_preserves _ _ (emit_preserves _ _)
      intro ignored
      exact pure_preserves _
    · intro ignored
      apply bind_preserves
      · apply forIn_preserves
        intro output accumulator
        apply bind_preserves _ _ (lowerExpr_preserves _)
        intro result
        exact pure_preserves _
      · intro outputs
        dsimp only
        split
        · apply bind_preserves _ _ (bindPublic_preserves _)
          intro ignored
          exact emit_preserves _ _
        · exact emit_preserves _ _

theorem lowerBody_next (circuit : Circuit) (state : Zkir.LowerState) :
    state.next ≤ ((Zkir.lowerBody circuit).run state).2.next :=
  (lowerBody_preserves circuit state).next

theorem lowerBody_allocated (circuit : Circuit) :
    ((Zkir.lowerBody circuit).run {}).2.next ≤ ((Zkir.lowerBody circuit).run {}).2.instructions.size := by
  have frame := (lowerBody_preserves circuit {}).instructions
  simpa using frame

theorem Frame.budget {before after : Zkir.LowerState} (frame : Frame before after)
    (limit : Nat) (bound : after.next ≤ limit) : before.next ≤ limit :=
  Nat.le_trans frame.next bound

/-- The state between two actual lowering computations is bounded by their
actual final state when the remaining computation preserves allocation order. -/
theorem bind_middle_frame (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState)
    (remaining : ∀ value, PreservesFrame (next value)) :
    Frame (first.run state).2 ((first >>= next).run state).2 := by
  change Frame (first.run state).2 ((next (first.run state).1).run (first.run state).2).2
  exact remaining _ _

theorem bind_middle_budget (first : StateM Zkir.LowerState α)
    (next : α → StateM Zkir.LowerState β) (state : Zkir.LowerState)
    (remaining : ∀ value, PreservesFrame (next value)) (limit : Nat)
    (bound : ((first >>= next).run state).2.next ≤ limit) :
    (first.run state).2.next ≤ limit :=
  (bind_middle_frame first next state remaining).budget limit bound

end Noctium.Verification.ScalarAllocation
