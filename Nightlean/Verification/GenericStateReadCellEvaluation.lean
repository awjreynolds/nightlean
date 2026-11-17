import Nightlean.Verification.GenericStateAdmission

namespace Nightlean.Verification.GenericStateReadCellEvaluation
open Backend ScalarNormalization

/-- Proof-facing spelling of the exact private nativeRead implementation. -/
def readExpression (ty : Ty) (name : String) : Expr .native :=
  match ty with
  | .native => .ref name
  | .bool => .cast .native (.ref name : Expr .bool)
  | .uint maximum => .cast .native (.ref name : Expr (.uint maximum))

theorem canonical_ref_eval (ctx : EvalContext) (env : EvalEnv)
    (name : String) (ty : Ty) (value : ty.Denote)
    (lookup : env.lookup name = some (Value.pack ty value))
    (modulus : ctx.modulus = Field.modulus) (canonical : Canonical ty value) :
    (Expr.ref name : Expr ty).eval ctx env = .ok value := by
  simp only [Expr.eval, lookup, number_pack_as]
  cases ty with
  | native =>
    have bound : value < ctx.modulus := by simpa [modulus, number] using canonical.1
    simp [canonical_eq, bound]
    rfl
  | bool => rfl
  | uint maximum =>
    have bound : value < ctx.modulus := by simpa [modulus, number] using canonical.1
    simp [canonical_eq, bound, canonical.2.1, canonical.2.2]
    rfl

/-- Native, Boolean and bounded integer read candidates retain their canonical
field representation through the actual cast used by Impact. -/
theorem readExpression_eval (ctx : EvalContext) (env : EvalEnv)
    (name : String) (ty : Ty) (value : ty.Denote)
    (lookup : env.lookup name = some (Value.pack ty value))
    (modulus : ctx.modulus = Field.modulus) (canonical : Canonical ty value) :
    (readExpression ty name).eval ctx env = .ok (number ty value) := by
  have reference := canonical_ref_eval ctx env name ty value lookup modulus canonical
  cases ty with
  | native => exact reference
  | bool =>
    simp only [readExpression]
    rw [Expr.eval, reference]
    simp only [bind, Except.bind]
    change (if (if value then 1 else 0) < ctx.modulus
      then Except.ok (if value then 1 else 0)
      else Except.error "noncanonical scalar conversion") =
      Except.ok (if value then 1 else 0)
    cases value <;> simp [modulus, Field.modulus]
  | uint maximum =>
    simp only [readExpression]
    rw [Expr.eval, reference]
    have bound : value < ctx.modulus := by simpa [modulus, number] using canonical.1
    change (if value < ctx.modulus then Except.ok value
      else Except.error "noncanonical scalar conversion") = Except.ok value
    simp [bound]

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- The actual emitted read-cell chunk compares against the canonical typed
candidate at its real declared slot. No source transition success is assumed. -/
theorem readCell_candidate_eval (state : List StateDecl)
    (name destination : String) (ty : Ty) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (value : ty.Denote)
    (accepted : Impact.appendEffect state (.readCell name destination ty) {} = .ok base)
    (lookup : env.lookup destination = some (Value.pack ty value))
    (modulus : ctx.modulus = Field.modulus) (canonical : Canonical ty value) :
    ∃ slot, state.findIdx? (·.name == name) = some slot ∧
      base.operations.mapM (GenericStateOps.evalOp ctx env) =
        .ok (GenericStateVM.readCellOps slot
          (NativeState.field (NativeRelation.scalar (number ty value)))) := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  obtain ⟨slot, found, equal⟩ := accepted
  cases equal
  have located : state.findIdx? (·.name == name) = some slot := by
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
  have evaluated := readExpression_eval ctx env destination ty value lookup modulus canonical
  change [Impact.Op.dup, .index slot,
      .popeq (.field (readExpression ty destination))].mapM
        (GenericStateOps.evalOp ctx env) = _
  simp [GenericStateVM.readCellOps, GenericStateOps.evalOp,
    GenericStateOps.evalAligned, evaluated, Except.map, Functor.map] <;> rfl

end Nightlean.Verification.GenericStateReadCellEvaluation
