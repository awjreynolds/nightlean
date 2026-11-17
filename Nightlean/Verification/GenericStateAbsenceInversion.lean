import Nightlean.Verification.GenericStateAbsenceAuthentication
import Nightlean.Verification.GenericStateWriteInversion

namespace Nightlean.Verification.GenericStateAbsenceInversion
open Backend

private theorem bind_ok {α β : Type} {first : Except ε α}
    {next : α → Except ε β} {result : β} :
    (first >>= next) = .ok result ↔
      ∃ value, first = .ok value ∧ next value = .ok result := by
  cases first <;> simp [Bind.bind, Except.bind]

private theorem mapM_member_success (operations : List Impact.Op)
    (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (evaluated : operations.mapM (GenericStateOps.evalOp ctx env) = .ok native) :
    ∀ operation ∈ operations, ∃ result,
      GenericStateOps.evalOp ctx env operation = .ok result := by
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

/-- A successful evaluation of the production absence segment forces its
original typed key expression to evaluate. -/
theorem requireAbsent_source_evaluates (state : List StateDecl) (name : String)
    (keyTy : Ty) (keyExpr : Expr keyTy) (base : Impact.Plan)
    (ctx : EvalContext) (env : EvalEnv) (native : List NativeState.Op)
    (accepted : Impact.appendEffect state
      (.requireAbsent name keyTy keyExpr) {} = .ok base)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : base.operations.mapM (GenericStateOps.evalOp ctx env) = .ok native) :
    ∃ key, keyExpr.eval ctx env = .ok key := by
  simp only [Impact.appendEffect, bind_ok] at accepted
  obtain ⟨slot, _, equal⟩ := accepted
  cases equal
  have member : Impact.Op.push
      (.field (GenericStateWriteInversion.scalarProjection keyTy keyExpr)) false ∈
      [Impact.Op.dup, .index slot,
        .push (.field (GenericStateWriteInversion.scalarProjection keyTy keyExpr)),
        .member, .popeq (.bit false)] := by simp
  obtain ⟨result, operationEval⟩ :=
    mapM_member_success _ ctx env native evaluated _ member
  cases source : (GenericStateWriteInversion.scalarProjection keyTy keyExpr).eval ctx env with
  | error message =>
    simp [GenericStateOps.evalOp, GenericStateOps.evalAligned,
      source, bind, Except.bind] at operationEval
  | ok number =>
    obtain ⟨key, sourceEval, _⟩ :=
      GenericStateWriteInversion.scalarProjection_invert ctx env keyTy keyExpr
        number modulus source
    exact ⟨key, sourceEval⟩

end Nightlean.Verification.GenericStateAbsenceInversion
