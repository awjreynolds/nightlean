import Noctium.Verification.GenericStateWriteEvaluation

namespace Noctium.Verification.GenericStateWriteInversion
open Backend ScalarNormalization

/-- Exact spelling of the scalar projection used by production write chunks. -/
def scalarProjection : (ty : Ty) → Expr ty → Expr .native
  | .native, expression => expression
  | .bool, expression => .select expression (.native 1) (.native 0)
  | .uint _, expression => .cast .native expression

/-- Successful evaluation of the actual field projection requires successful
source evaluation and preserves its number. No source success is assumed. -/
theorem scalarProjection_invert (ctx : EvalContext) (env : EvalEnv)
    (ty : Ty) (expression : Expr ty) (number : Nat)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : (scalarProjection ty expression).eval ctx env = .ok number) :
    ∃ value, expression.eval ctx env = .ok value ∧ number = ScalarNormalization.number ty value := by
  cases ty with
  | native => exact ⟨number, evaluated, rfl⟩
  | bool =>
    cases source : expression.eval ctx env with
    | error message =>
      simp [scalarProjection, Expr.eval, source, bind, Except.bind] at evaluated
    | ok value =>
      have projected : (scalarProjection .bool expression).eval ctx env =
          .ok (ScalarNormalization.number .bool value) := by
        cases value <;> simp [scalarProjection, Expr.eval, source,
          modulus, Field.modulus, ScalarNormalization.number, bind, Except.bind] <;> rfl
      rw [projected] at evaluated
      exact ⟨value, rfl, (Except.ok.inj evaluated).symm⟩
  | uint maximum =>
    cases source : expression.eval ctx env with
    | error message =>
      simp [scalarProjection, Expr.eval, source, bind, Except.bind] at evaluated
    | ok value =>
      simp only [scalarProjection] at evaluated
      rw [Expr.eval, source] at evaluated
      change (if value < ctx.modulus then Except.ok value
        else Except.error "noncanonical scalar conversion") = .ok number at evaluated
      split at evaluated
      · exact ⟨value, rfl, (Except.ok.inj evaluated).symm⟩
      · cases evaluated

private theorem mapM_member_success (operations : List Impact.Op)
    (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (evaluated : operations.mapM (GenericStateOps.evalOp ctx env) = .ok native) :
    ∀ operation ∈ operations, ∃ result, GenericStateOps.evalOp ctx env operation = .ok result := by
  induction operations generalizing native with
  | nil => simp
  | cons head rest ih =>
    simp only [List.mapM_cons] at evaluated
    cases first : GenericStateOps.evalOp ctx env head with
    | error message => simp [first, bind, Except.bind] at evaluated
    | ok result =>
      cases later : rest.mapM (GenericStateOps.evalOp ctx env) with
      | error message => simp [first, later, bind, Except.bind] at evaluated
      | ok results =>
        intro operation member
        rcases List.mem_cons.mp member with equal | present
        · subst operation
          exact ⟨result, first⟩
        · exact ih results later operation present

private theorem eval_push_source (ctx : EvalContext) (env : EvalEnv)
    (expression : Expr .native) (storage : Bool) (result : NativeState.Op)
    (evaluated : GenericStateOps.evalOp ctx env (.push (.field expression) storage) = .ok result) :
    ∃ number, expression.eval ctx env = .ok number := by
  cases source : expression.eval ctx env with
  | error message =>
    simp [GenericStateOps.evalOp, GenericStateOps.evalAligned,
      source, bind, Except.bind] at evaluated
  | ok number => exact ⟨number, rfl⟩

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

/-- An accepted, successfully evaluated production cell-write segment forces
the original typed source expression to evaluate. -/
theorem writeCell_source_evaluates (state : List StateDecl) (name : String)
    (ty : Ty) (expression : Expr ty) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (accepted : Impact.appendEffect state (.writeCell name ty expression) {} = .ok base)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx env) = .ok native) :
    ∃ value, expression.eval ctx env = .ok value := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  obtain ⟨slot, _, equal⟩ := accepted
  cases equal
  have member : Impact.Op.push (.field (scalarProjection ty expression)) true ∈
      [Impact.Op.push (.field (.native slot)),
        .push (.field (scalarProjection ty expression)) true, .insert 1] := by simp
  obtain ⟨operation, operationEval⟩ := mapM_member_success _ ctx env native evaluated _ member
  obtain ⟨number, projected⟩ := eval_push_source ctx env _ true operation operationEval
  obtain ⟨value, source, _⟩ := scalarProjection_invert ctx env ty expression number modulus projected
  exact ⟨value, source⟩

/-- Both typed source map-write expressions evaluate whenever the actual
production key/value pushes evaluate successfully. -/
theorem writeMap_source_evaluates (state : List StateDecl) (name : String)
    (keyTy valueTy : Ty) (keyExpr : Expr keyTy) (valueExpr : Expr valueTy)
    (base : Impact.Plan) (ctx : EvalContext) (env : EvalEnv)
    (native : List NativeState.Op)
    (accepted : Impact.appendEffect state
      (.writeMap name keyTy valueTy keyExpr valueExpr) {} = .ok base)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx env) = .ok native) :
    ∃ key value, keyExpr.eval ctx env = .ok key ∧ valueExpr.eval ctx env = .ok value := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  obtain ⟨slot, _, equal⟩ := accepted
  cases equal
  have keyMember : Impact.Op.push (.field (scalarProjection keyTy keyExpr)) false ∈
      [Impact.Op.index slot true, .push (.field (scalarProjection keyTy keyExpr)),
        .push (.field (scalarProjection valueTy valueExpr)) true, .insert 2] := by simp
  have valueMember : Impact.Op.push (.field (scalarProjection valueTy valueExpr)) true ∈
      [Impact.Op.index slot true, .push (.field (scalarProjection keyTy keyExpr)),
        .push (.field (scalarProjection valueTy valueExpr)) true, .insert 2] := by simp
  obtain ⟨keyOp, keyOpEval⟩ := mapM_member_success _ ctx env native evaluated _ keyMember
  obtain ⟨valueOp, valueOpEval⟩ := mapM_member_success _ ctx env native evaluated _ valueMember
  obtain ⟨keyNumber, keyProjection⟩ := eval_push_source ctx env _ false keyOp keyOpEval
  obtain ⟨valueNumber, valueProjection⟩ := eval_push_source ctx env _ true valueOp valueOpEval
  obtain ⟨key, keyEval, _⟩ := scalarProjection_invert ctx env keyTy keyExpr keyNumber modulus keyProjection
  obtain ⟨value, valueEval, _⟩ := scalarProjection_invert ctx env valueTy valueExpr valueNumber modulus valueProjection
  exact ⟨key, value, keyEval, valueEval⟩

end Noctium.Verification.GenericStateWriteInversion
