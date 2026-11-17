import Nightlean.Verification.GenericStateAdmission

namespace Nightlean.Verification.GenericStateWriteEvaluation
open Backend ScalarNormalization

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]


/-- A typed canonical cell write evaluates to the actual emitted slot and
value, with the slot bound derived from the admitted declaration count. -/
theorem writeCell_candidate_eval_located (state : List StateDecl) (name : String)
    (ty : Ty) (expression : Expr ty) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (value : ty.Denote)
    (accepted : Impact.appendEffect state (.writeCell name ty expression) {} = .ok base)
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : expression.eval ctx env = .ok value)
    (canonical : Canonical ty value) :
    ∃ slot declaration, state.findIdx? (·.name == name) = some slot ∧
      state[slot]? = some declaration ∧ declaration.name = name ∧ slot < state.length ∧
      base.operations.mapM (GenericStateOps.evalOp ctx env) =
        .ok (GenericStateVM.writeCellOps slot
          (NativeState.field (NativeRelation.scalar (number ty value)))) := by
  obtain ⟨slot, nativeExpr, shape, meaning⟩ :=
    GenericStateAdmission.writeCell_chunk state name ty expression base ctx env value accepted
  obtain ⟨actualSlot, declaration, actualExpr, located, named, inside, actualShape⟩ :=
    GenericStateAdmission.writeCell_chunk_slot state name ty expression base accepted
  have same : slot = actualSlot := by
    have first := (List.cons.inj (shape.symm.trans actualShape)).1
    exact Expr.native.inj (Impact.Aligned.field.inj (Impact.Op.push.inj first).1)
  subst actualSlot
  have impactLocated : state.findIdx? (·.name == name) = some slot := by
    simp only [Impact.appendEffect, bind_ok] at accepted
    obtain ⟨emitted, found, equal⟩ := accepted
    cases equal
    have same : emitted = slot := by
      have first := (List.cons.inj shape).1
      exact Expr.native.inj (Impact.Aligned.field.inj (Impact.Op.push.inj first).1)
    subst emitted
    change (match state.findIdx? (·.name == name) with
      | some index => (pure index : Except String Nat)
      | none => throw s!"unknown ledger state '{name}'") = .ok slot at found
    cases index : state.findIdx? (·.name == name) with
    | none => simp [index] at found
    | some actual =>
      simp [index] at found
      cases found
      rfl
  refine ⟨slot, declaration, impactLocated, located, named, inside, ?_⟩
  rw [shape]
  have nativeValue := meaning modulus evaluated canonical
  have slotBound := Nat.lt_trans inside stateBound
  have slotEval : (Expr.native slot : Expr .native).eval ctx env = .ok slot := by
    simp [Expr.eval, modulus, slotBound] <;> rfl
  simp [GenericStateVM.writeCellOps, GenericStateOps.evalOp,
    GenericStateOps.evalAligned, slotEval, nativeValue,
    Except.map, Functor.map] <;> rfl

/-- The original write-cell evaluation interface, retaining declaration
identity while the located companion also exposes production findIdx?. -/
theorem writeCell_candidate_eval (state : List StateDecl) (name : String)
    (ty : Ty) (expression : Expr ty) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (value : ty.Denote)
    (accepted : Impact.appendEffect state (.writeCell name ty expression) {} = .ok base)
    (stateBound : state.length < Field.modulus)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : expression.eval ctx env = .ok value)
    (canonical : Canonical ty value) :
    ∃ slot declaration, state[slot]? = some declaration ∧
      declaration.name = name ∧ slot < state.length ∧
      base.operations.mapM (GenericStateOps.evalOp ctx env) =
        .ok (GenericStateVM.writeCellOps slot
          (NativeState.field (NativeRelation.scalar (number ty value)))) := by
  obtain ⟨slot, declaration, _, facts⟩ := writeCell_candidate_eval_located
    state name ty expression base ctx env value accepted stateBound modulus evaluated canonical
  exact ⟨slot, declaration, facts⟩

/-- Map key and value projection preserve their canonical field encodings at
the exact slot selected by production state lookup. -/
theorem writeMap_candidate_eval (state : List StateDecl) (name : String)
    (keyTy valueTy : Ty) (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (base : Impact.Plan) (ctx : EvalContext) (env : EvalEnv)
    (key : keyTy.Denote) (value : valueTy.Denote)
    (accepted : Impact.appendEffect state
      (.writeMap name keyTy valueTy keyExpr valueExpr) {} = .ok base)
    (modulus : ctx.modulus = Field.modulus)
    (keyEval : keyExpr.eval ctx env = .ok key)
    (valueEval : valueExpr.eval ctx env = .ok value)
    (keyCanonical : Canonical keyTy key) (valueCanonical : Canonical valueTy value) :
    ∃ slot, state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx env) =
        .ok (GenericStateVM.writeMapOps slot
          (NativeRelation.scalar (number keyTy key))
          (NativeRelation.scalar (number valueTy value))) := by
  obtain ⟨slot, nativeKey, nativeValue, shape, keyMeaning, valueMeaning⟩ :=
    GenericStateAdmission.writeMap_chunk state name keyTy valueTy keyExpr valueExpr
      base ctx env key value accepted
  have located : state.findIdx? (·.name == name) = some slot := by
    simp only [Impact.appendEffect, bind_ok] at accepted
    obtain ⟨actualSlot, found, equal⟩ := accepted
    cases equal
    have same : actualSlot = slot := by
      exact (Impact.Op.index.inj (List.cons.inj shape).1).1
    subst actualSlot
    change (match state.findIdx? (·.name == name) with
      | some index => (pure index : Except String Nat)
      | none => throw s!"unknown ledger state '{name}'") = .ok slot at found
    cases index : state.findIdx? (·.name == name) with
    | none => simp [index] at found
    | some actual =>
      simp [index] at found
      cases found
      rfl
  refine ⟨slot, located, ?_⟩
  rw [shape]
  have keyNative := keyMeaning modulus keyEval keyCanonical
  have valueNative := valueMeaning modulus valueEval valueCanonical
  simp [GenericStateVM.writeMapOps, GenericStateOps.evalOp,
    GenericStateOps.evalAligned, keyNative, valueNative,
    Except.map, Functor.map] <;> rfl

end Nightlean.Verification.GenericStateWriteEvaluation
