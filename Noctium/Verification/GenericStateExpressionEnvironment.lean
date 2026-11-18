import Noctium.Semantics
namespace Noctium.Verification.GenericStateExpressionEnvironment
 /-- Evaluation depends only on first-match value lookup, including under
 local let bindings and eager select branches. -/
 theorem eval_lookup_ext (ctx : EvalContext) (expression : Expr ty)
    (left right : EvalEnv)
    (agreement : ∀ name, left.lookup name = right.lookup name) :
    expression.eval ctx left = expression.eval ctx right := by
  induction expression generalizing left right with
  | native n => rfl
  | bool b => rfl
  | uint maximum value => rfl
  | ref name => simp [Expr.eval, agreement name]
  | add a b ia ib => simp [Expr.eval, ia left right agreement, ib left right agreement]
  | mul a b ia ib => simp [Expr.eval, ia left right agreement, ib left right agreement]
  | sub a b ia ib => simp [Expr.eval, ia left right agreement, ib left right agreement]
  | uadd a b ia ib => simp [Expr.eval, ia left right agreement, ib left right agreement]
  | usub a b ia ib => simp [Expr.eval, ia left right agreement, ib left right agreement]
  | umul a b ia ib => simp [Expr.eval, ia left right agreement, ib left right agreement]
  | cast target value ih => simp [Expr.eval, ih left right agreement]
  | letE name value body ihValue ihBody =>
    have extended (raw : Value) :
        ∀ found, ((name, raw) :: left).lookup found =
          ((name, raw) :: right).lookup found := by
      intro found
      by_cases same : found = name
      · subst found
        simp
      · have unequal : (found == name) = false := by simp [same]
        simp [List.lookup_cons, unequal, agreement found]
    simp only [Expr.eval, ihValue left right agreement]
    cases evaluated : value.eval ctx right with
    | error message => simp [bind, Except.bind]
    | ok raw =>
      simp only [bind, Except.bind]
      exact ihBody _ _ (extended _)
  | assertE condition body ic ib => simp [Expr.eval, ic left right agreement, ib left right agreement]
  | disclose span value ih => simp [Expr.eval, ih left right agreement]
  | eq a b ia ib => simp [Expr.eval, ia left right agreement, ib left right agreement]
  | select c a b ic ia ib => simp [Expr.eval, ic left right agreement, ia left right agreement, ib left right agreement]
  | poseidon2 domain a b ia ib => simp [Expr.eval, ia left right agreement, ib left right agreement]
end Noctium.Verification.GenericStateExpressionEnvironment
