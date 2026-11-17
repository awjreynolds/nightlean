import Nightlean.Semantics

namespace Nightlean.Verification.GenericStateExpressionScope

private theorem exceptBindOk {ε : Type} {α β : Type}
    (first : Except ε α) (next : α → Except ε β) (value : β) :
    Except.bind first next = .ok value ↔
      ∃ intermediate, first = .ok intermediate ∧ next intermediate = .ok value := by
  cases first <;> simp [Except.bind]

private theorem exceptUnitBind (first next : Except String Unit) :
    Except.bind first (fun _ => next) = .ok () ↔ first = .ok () ∧ next = .ok () := by
  cases first <;> simp [Except.bind]

private theorem guardedPairOk (guard : Bool) (message : String)
    (first second : Except String Unit)
    (valid : (if !guard then .error message else
      Except.bind first (fun _ => second)) = .ok ()) :
    first = .ok () ∧ second = .ok () := by
  cases guard with
  | false => simp at valid
  | true =>
    simp only [Bool.not_true] at valid
    exact exceptUnitBind first second |>.mp valid

private theorem lookupNameMem (types : TypeEnv) (name : String) (ty : Ty)
    (lookup : types.lookup name = some ty) : name ∈ types.map Prod.fst := by
  obtain ⟨before, after, equal, _⟩ := List.lookup_eq_some_iff.mp lookup
  rw [equal]
  simp

private theorem extendAgreement (types : TypeEnv) (left right : EvalEnv)
    (agreement : ∀ name ∈ types.map Prod.fst, left.lookup name = right.lookup name)
    (name : String) (source : Ty) (raw : Value) :
    ∀ found ∈ ((name, source) :: types).map Prod.fst,
      ((name, raw) :: left).lookup found = ((name, raw) :: right).lookup found := by
  intro found member
  simp only [List.map_cons] at member
  rcases List.mem_cons.mp member with same | inTypes
  · subst found
    simp
  · by_cases same : found = name
    · subst found
      simp
    · have unequal : (found == name) = false := by simp [same]
      simp only [List.lookup_cons, unequal]
      exact agreement found inTypes

/-- Validation limits expression dependencies to the declared type scope.
Evaluation therefore agrees across environments that agree on those names.
Local lets extend both scopes with the same evaluated value. -/
theorem eval_agree_of_valid (expression : Expr ty) (caps : Capabilities)
    (types : TypeEnv) (ctx : EvalContext) (left right : EvalEnv)
    (valid : expression.validate caps types = .ok ())
    (agreement : ∀ name ∈ types.map Prod.fst, left.lookup name = right.lookup name) :
    expression.eval ctx left = expression.eval ctx right := by
  induction expression generalizing types left right with
  | native value => rfl
  | bool value => rfl
  | uint maximum value => rfl
  | @ref ty name =>
    have lookup : ∃ foundTy, types.lookup name = some foundTy := by
      simp only [Expr.validate, bind, exceptBindOk] at valid
      rcases valid with ⟨_, typeValid, referenceValid⟩
      cases found : types.lookup name with
      | none => simp [found] at referenceValid
      | some foundTy => exact ⟨foundTy, rfl⟩
    obtain ⟨foundTy, lookup⟩ := lookup
    have member := lookupNameMem types name foundTy lookup
    simp [Expr.eval, agreement name member]
  | add a b ihA ihB =>
    have validations : a.validate caps types = .ok () ∧ b.validate caps types = .ok () := by
      change (if !caps.nativeArithmetic then .error "target lacks native arithmetic" else
        Except.bind (a.validate caps types) (fun _ => b.validate caps types)) = .ok () at valid
      by_cases arithmetic : caps.nativeArithmetic
      · simp only [show (!caps.nativeArithmetic) = false by simp [arithmetic]] at valid
        exact exceptUnitBind _ _ |>.mp valid
      · simp [arithmetic] at valid
    simp [Expr.eval, ihA types left right validations.1 agreement,
      ihB types left right validations.2 agreement]
  | mul a b ihA ihB =>
    have validations : a.validate caps types = .ok () ∧ b.validate caps types = .ok () := by
      change (if !caps.nativeArithmetic then .error "target lacks native arithmetic" else
        Except.bind (a.validate caps types) (fun _ => b.validate caps types)) = .ok () at valid
      by_cases arithmetic : caps.nativeArithmetic
      · simp only [show (!caps.nativeArithmetic) = false by simp [arithmetic]] at valid
        exact exceptUnitBind _ _ |>.mp valid
      · simp [arithmetic] at valid
    simp [Expr.eval, ihA types left right validations.1 agreement,
      ihB types left right validations.2 agreement]
  | sub a b ihA ihB =>
    have validations : a.validate caps types = .ok () ∧ b.validate caps types = .ok () := by
      change (if !caps.nativeArithmetic then .error "target lacks native arithmetic" else
        Except.bind (a.validate caps types) (fun _ => b.validate caps types)) = .ok () at valid
      by_cases arithmetic : caps.nativeArithmetic
      · simp only [show (!caps.nativeArithmetic) = false by simp [arithmetic]] at valid
        exact exceptUnitBind _ _ |>.mp valid
      · simp [arithmetic] at valid
    simp [Expr.eval, ihA types left right validations.1 agreement,
      ihB types left right validations.2 agreement]
  | uadd a b ihA ihB =>
    have validations : a.validate caps types = .ok () ∧ b.validate caps types = .ok () := by
      change Except.bind ((Ty.uint _).validate caps) (fun _ =>
        if !caps.nativeArithmetic then .error "target lacks native arithmetic" else
          Except.bind (a.validate caps types) (fun _ => b.validate caps types)) = .ok () at valid
      rw [exceptUnitBind] at valid
      rcases valid with ⟨_, arithmeticValid⟩
      by_cases arithmetic : caps.nativeArithmetic
      · simp only [show (!caps.nativeArithmetic) = false by simp [arithmetic]] at arithmeticValid
        exact exceptUnitBind _ _ |>.mp arithmeticValid
      · simp [arithmetic] at arithmeticValid
    simp [Expr.eval, ihA types left right validations.1 agreement,
      ihB types left right validations.2 agreement]
  | usub a b ihA ihB =>
    have validations : a.validate caps types = .ok () ∧ b.validate caps types = .ok () := by
      change Except.bind ((Ty.uint _).validate caps) (fun _ =>
        if !caps.nativeArithmetic then .error "target lacks native arithmetic" else
          Except.bind (a.validate caps types) (fun _ => b.validate caps types)) = .ok () at valid
      rw [exceptUnitBind] at valid
      rcases valid with ⟨_, arithmeticValid⟩
      by_cases arithmetic : caps.nativeArithmetic
      · simp only [show (!caps.nativeArithmetic) = false by simp [arithmetic]] at arithmeticValid
        exact exceptUnitBind _ _ |>.mp arithmeticValid
      · simp [arithmetic] at arithmeticValid
    simp [Expr.eval, ihA types left right validations.1 agreement,
      ihB types left right validations.2 agreement]
  | umul a b ihA ihB =>
    have validations : a.validate caps types = .ok () ∧ b.validate caps types = .ok () := by
      change Except.bind ((Ty.uint _).validate caps) (fun _ =>
        if !caps.nativeArithmetic then .error "target lacks native arithmetic" else
          Except.bind (a.validate caps types) (fun _ => b.validate caps types)) = .ok () at valid
      rw [exceptUnitBind] at valid
      rcases valid with ⟨_, arithmeticValid⟩
      by_cases arithmetic : caps.nativeArithmetic
      · simp only [show (!caps.nativeArithmetic) = false by simp [arithmetic]] at arithmeticValid
        exact exceptUnitBind _ _ |>.mp arithmeticValid
      · simp [arithmetic] at arithmeticValid
    simp [Expr.eval, ihA types left right validations.1 agreement,
      ihB types left right validations.2 agreement]
  | cast target value ih =>
    have valueValid : value.validate caps types = .ok () := by
      change Except.bind (target.validate caps) (fun _ => value.validate caps types) = .ok () at valid
      exact (exceptUnitBind _ _).mp valid |>.2
    simp [Expr.eval, ih types left right valueValid agreement]
  | @letE source resultTy name value body ihValue ihBody =>
    have validations : value.validate caps types = .ok () ∧
        body.validate caps ((name, source) :: types) = .ok () := by
      change Except.bind (value.validate caps types)
        (fun _ => body.validate caps ((name, source) :: types)) = .ok () at valid
      exact (exceptUnitBind _ _).mp valid
    have valueEqual := ihValue types left right validations.1 agreement
    simp only [Expr.eval]
    rw [valueEqual]
    cases evaluated : value.eval ctx right with
    | error message => simp [bind, Except.bind]
    | ok raw =>
      simp only [bind, Except.bind]
      exact ihBody ((name, source) :: types)
        ((name, Value.pack source raw) :: left)
        ((name, Value.pack source raw) :: right) validations.2
        (extendAgreement types left right agreement name source (Value.pack source raw))
  | assertE condition body ihCondition ihBody =>
    have validations : condition.validate caps types = .ok () ∧ body.validate caps types = .ok () := by
      change Except.bind (condition.validate caps types)
        (fun _ => body.validate caps types) = .ok () at valid
      exact (exceptUnitBind _ _).mp valid
    simp [Expr.eval,
      ihCondition types left right validations.1 agreement,
      ihBody types left right validations.2 agreement]
  | disclose span value ih =>
    have valueValid : value.validate caps types = .ok () := by
      simpa only [Expr.validate] using valid
    simp [Expr.eval, ih types left right valueValid agreement]
  | eq a b ihA ihB =>
    have validations : a.validate caps types = .ok () ∧ b.validate caps types = .ok () := by
      change (if !caps.equality then .error "target lacks equality" else
        Except.bind (a.validate caps types) (fun _ => b.validate caps types)) = .ok () at valid
      by_cases equality : caps.equality
      · simp only [show (!caps.equality) = false by simp [equality]] at valid
        exact exceptUnitBind _ _ |>.mp valid
      · simp [equality] at valid
    simp [Expr.eval, ihA types left right validations.1 agreement,
      ihB types left right validations.2 agreement]
  | select condition yes no ihCondition ihYes ihNo =>
    have validations : condition.validate caps types = .ok () ∧
        yes.validate caps types = .ok () ∧ no.validate caps types = .ok () := by
      change (if !caps.select then .error "target lacks conditional selection" else
        Except.bind (condition.validate caps types) (fun _ =>
          Except.bind (yes.validate caps types) (fun _ => no.validate caps types))) = .ok () at valid
      by_cases selection : caps.select
      · simp only [show (!caps.select) = false by simp [selection]] at valid
        rcases (exceptUnitBind _ _).mp valid with ⟨conditionValid, remainderValid⟩
        rcases (exceptUnitBind _ _).mp remainderValid with ⟨yesValid, noValid⟩
        exact ⟨conditionValid, yesValid, noValid⟩
      · simp [selection] at valid
    simp [Expr.eval,
      ihCondition types left right validations.1 agreement,
      ihYes types left right validations.2.1 agreement,
      ihNo types left right validations.2.2 agreement]
  | poseidon2 domain a b ihA ihB =>
    have validations : a.validate caps types = .ok () ∧ b.validate caps types = .ok () := by
      change (if domain >= caps.nativeModulus then .error "noncanonical Poseidon domain" else
        if !caps.poseidon2 then .error "target lacks qualified Poseidon support" else
          Except.bind (a.validate caps types) (fun _ => b.validate caps types)) = .ok () at valid
      by_cases domainOk : domain < caps.nativeModulus
      · have domainGuard : ¬ domain >= caps.nativeModulus := by omega
        simp only [ite_eq_right domainGuard] at valid
        by_cases poseidon : caps.poseidon2
        · simp only [show (!caps.poseidon2) = false by simp [poseidon]] at valid
          exact exceptUnitBind _ _ |>.mp valid
        · simp [poseidon] at valid
      · have domainGuard : domain >= caps.nativeModulus := by omega
        simp [domainGuard] at valid
    simp [Expr.eval, ihA types left right validations.1 agreement,
      ihB types left right validations.2 agreement]

#print axioms eval_agree_of_valid

end Nightlean.Verification.GenericStateExpressionScope
