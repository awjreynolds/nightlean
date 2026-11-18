import Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.GenericStateEvaluationCanonical

open ScalarNormalization

private def scalarCastView (ctx : EvalContext) (target : Ty) (number : Nat) :
    Except String target.Denote :=
  match target with
  | .native =>
    if number < ctx.modulus then .ok number
    else .error "noncanonical scalar conversion"
  | .bool => .ok (number != 0)
  | .uint maximum =>
    if maximum ≤ ScalarPolicy.maxUint && number ≤ maximum && number < ctx.modulus then
      .ok number
    else .error "scalar conversion exceeds unsigned bound"

private theorem scalarCastView_canonical (ctx : EvalContext) (target : Ty)
    (number : Nat) (value : target.Denote)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : scalarCastView ctx target number = .ok value) :
    Canonical target value := by
  cases target with
  | native =>
    change (if number < ctx.modulus then (Except.ok number : Except String Nat)
      else (Except.error "noncanonical scalar conversion" : Except String Nat)) =
        .ok value at evaluated
    have bound : number < ctx.modulus := by
      by_cases h : number < ctx.modulus
      · exact h
      · simp [h] at evaluated
    have equality : value = number := by
      simp [bound] at evaluated
      exact evaluated.symm
    subst value
    exact ⟨by simpa [ScalarNormalization.number, modulus] using bound, trivial⟩
  | bool =>
    cases value <;>
      simp [Canonical, ScalarNormalization.number, Field.modulus]
  | uint maximum =>
    change (if maximum ≤ ScalarPolicy.maxUint && number ≤ maximum && number < ctx.modulus
      then (Except.ok number : Except String Nat)
      else (Except.error "scalar conversion exceeds unsigned bound" : Except String Nat)) =
        .ok value at evaluated
    have maximumBound : maximum ≤ ScalarPolicy.maxUint := by
      by_cases h : maximum ≤ ScalarPolicy.maxUint
      · exact h
      · simp [h] at evaluated
    have valueBound : number ≤ maximum := by
      by_cases h : number ≤ maximum
      · exact h
      · simp [maximumBound, h] at evaluated
    have fieldBound : number < ctx.modulus := by
      by_cases h : number < ctx.modulus
      · exact h
      · simp [maximumBound, valueBound, h] at evaluated
    have equality : value = number := by
      simp [maximumBound, valueBound, fieldBound] at evaluated
      exact evaluated.symm
    subst value
    exact ⟨by simpa [ScalarNormalization.number, modulus] using fieldBound,
      maximumBound, valueBound⟩

private theorem canonical_native_of_bound (value : Nat) (bound : value < Field.modulus) :
    Canonical .native value := by
  exact ⟨by simpa [ScalarNormalization.number] using bound, trivial⟩

/-- Successful expression evaluation under the production field modulus always
returns a value in the source type's canonical range. -/
theorem expression_eval_canonical (ctx : EvalContext) (env : EvalEnv)
    (expression : Expr ty) (value : ty.Denote)
    (modulus : ctx.modulus = Field.modulus)
    (evaluated : expression.eval ctx env = .ok value) :
    Canonical ty value := by
  induction expression generalizing env with
  | native number =>
    simp only [Expr.eval] at evaluated
    change (if number < ctx.modulus then (Except.ok number : Except String Nat)
      else (Except.error "noncanonical native constant" : Except String Nat)) =
        .ok value at evaluated
    have bound : number < ctx.modulus := by
      by_cases h : number < ctx.modulus
      · exact h
      · simp [h] at evaluated
    have equality : value = number := by
      simp [bound] at evaluated
      exact evaluated.symm
    subst value
    exact canonical_native_of_bound number (by simpa [modulus] using bound)
  | bool value =>
    have equality := Except.ok.inj evaluated
    subst value
    cases value <;> simp [Canonical, ScalarNormalization.number, Field.modulus]
  | uint maximum number =>
    simp only [Expr.eval, canonical_eq] at evaluated
    have maximumBound : maximum ≤ ScalarPolicy.maxUint := by
      by_cases bound : maximum ≤ ScalarPolicy.maxUint
      · exact bound
      · simp [bound] at evaluated
    have valueBound : number ≤ maximum := by
      by_cases bound : number ≤ maximum
      · exact bound
      · simp [bound] at evaluated
    have fieldBound : number < ctx.modulus := by
      by_cases bound : number < ctx.modulus
      · exact bound
      · simp [bound] at evaluated
    have equality : value = number := by
      simp [maximumBound, valueBound, fieldBound] at evaluated
      exact (Except.ok.inj evaluated).symm
    subst value
    exact ⟨by simpa [ScalarNormalization.number, modulus] using fieldBound,
      maximumBound, valueBound⟩
  | @ref refTy name =>
    cases refTy with
    | native =>
      simp only [Expr.eval, canonical_eq] at evaluated
      cases lookup : env.lookup name with
      | none => simp [lookup] at evaluated
      | some raw =>
        cases typed : raw.as .native with
        | none => simp [lookup, typed] at evaluated
        | some found =>
          have bound : found < ctx.modulus := by
            by_cases bound : found < ctx.modulus
            · exact bound
            · simp [lookup, typed, bound] at evaluated
              cases evaluated
          have equality : value = found := by
            simp [lookup, typed, bound] at evaluated
            change (Except.ok found : Except String Nat) = .ok value at evaluated
            exact (Except.ok.inj evaluated).symm
          subst value
          exact ⟨by simpa [ScalarNormalization.number, modulus] using bound, trivial⟩
    | bool =>
      cases value <;> simp [Canonical, ScalarNormalization.number, Field.modulus]
    | uint maximum =>
      cases lookup : env.lookup name with
      | none => simp [Expr.eval, lookup] at evaluated
      | some raw =>
        cases typed : raw.as (.uint maximum) with
        | none => simp [Expr.eval, lookup, typed] at evaluated
        | some found =>
          have maximumBound : maximum ≤ ScalarPolicy.maxUint := by
            by_cases bound : maximum ≤ ScalarPolicy.maxUint
            · exact bound
            · simp [Expr.eval, lookup, typed, canonical_eq, bound,
                bind, Except.bind] at evaluated
          have valueBound : found ≤ maximum := by
            by_cases bound : found ≤ maximum
            · exact bound
            · simp [Expr.eval, lookup, typed, canonical_eq, bound,
                bind, Except.bind] at evaluated
          have fieldBound : found < ctx.modulus := by
            by_cases bound : found < ctx.modulus
            · exact bound
            · simp [Expr.eval, lookup, typed, canonical_eq, bound,
                bind, Except.bind] at evaluated
          have equality : value = found := by
            simp [Expr.eval, lookup, typed, canonical_eq, maximumBound, valueBound,
              fieldBound] at evaluated
            change (Except.ok found : Except String Nat) = .ok value at evaluated
            exact (Except.ok.inj evaluated).symm
          subst value
          exact ⟨by simpa [ScalarNormalization.number, modulus] using fieldBound,
            maximumBound, valueBound⟩
  | add left right ihLeft ihRight =>
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, leftEval, modulus, Field.modulus,
        bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, leftEval, rightEval, modulus, Field.modulus,
          bind, Bind.bind, Except.bind] at evaluated
      | ok rightValue =>
        simp [Expr.eval, leftEval, rightEval, modulus, Field.modulus,
          bind, Bind.bind, Except.bind] at evaluated
        change (Except.ok ((leftValue + rightValue) % Field.modulus) : Except String Nat) =
          .ok value at evaluated
        have resultEq : (leftValue + rightValue) % Field.modulus = value :=
          Except.ok.inj evaluated
        subst value
        exact canonical_native_of_bound _ (Nat.mod_lt _ (by decide))
  | mul left right ihLeft ihRight =>
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, leftEval, modulus, Field.modulus,
        bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, leftEval, rightEval, modulus, Field.modulus,
          bind, Bind.bind, Except.bind] at evaluated
      | ok rightValue =>
        simp [Expr.eval, leftEval, rightEval, modulus, Field.modulus,
          bind, Bind.bind, Except.bind] at evaluated
        change (Except.ok ((leftValue * rightValue) % Field.modulus) : Except String Nat) =
          .ok value at evaluated
        have resultEq : (leftValue * rightValue) % Field.modulus = value :=
          Except.ok.inj evaluated
        subst value
        exact canonical_native_of_bound _ (Nat.mod_lt _ (by decide))
  | sub left right ihLeft ihRight =>
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, leftEval, modulus, Field.modulus,
        bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, leftEval, rightEval, modulus, Field.modulus,
          bind, Bind.bind, Except.bind] at evaluated
      | ok rightValue =>
        simp [Expr.eval, leftEval, rightEval, modulus, Field.modulus,
          bind, Bind.bind, Except.bind] at evaluated
        change (Except.ok ((Field.modulus + leftValue - rightValue) % Field.modulus) :
          Except String Nat) = .ok value at evaluated
        have resultEq : (Field.modulus + leftValue - rightValue) % Field.modulus = value :=
          Except.ok.inj evaluated
        subst value
        exact canonical_native_of_bound _ (Nat.mod_lt _ (by decide))
  | uadd left right ihLeft ihRight =>
    rename_i leftMaximum rightMaximum
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, leftEval, bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, leftEval, rightEval, bind, Bind.bind, Except.bind] at evaluated
      | ok rightValue =>
        simp only [Expr.eval, leftEval, rightEval, bind, Bind.bind, Except.bind] at evaluated
        change scalarCastView ctx (.uint (leftMaximum + rightMaximum))
          (leftValue + rightValue) = .ok value at evaluated
        exact scalarCastView_canonical ctx (.uint (leftMaximum + rightMaximum))
          (leftValue + rightValue) value modulus evaluated
  | usub left right ihLeft ihRight =>
    rename_i leftMaximum rightMaximum
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, leftEval, bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, leftEval, rightEval, bind, Bind.bind, Except.bind] at evaluated
      | ok rightValue =>
        have noUnderflow : ¬ leftValue < rightValue := by
          by_cases underflow : leftValue < rightValue
          · simp [Expr.eval, leftEval, rightEval, underflow, bind, Bind.bind,
              Except.bind] at evaluated
          · exact underflow
        simp only [Expr.eval, leftEval, rightEval, noUnderflow, bind, Bind.bind,
          Except.bind] at evaluated
        change scalarCastView ctx (.uint leftMaximum) (leftValue - rightValue) =
          .ok value at evaluated
        exact scalarCastView_canonical ctx (.uint leftMaximum)
          (leftValue - rightValue) value modulus evaluated
  | umul left right ihLeft ihRight =>
    rename_i leftMaximum rightMaximum
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, leftEval, bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, leftEval, rightEval, bind, Bind.bind, Except.bind] at evaluated
      | ok rightValue =>
        simp only [Expr.eval, leftEval, rightEval, bind, Bind.bind, Except.bind] at evaluated
        change scalarCastView ctx (.uint (leftMaximum * rightMaximum))
          (leftValue * rightValue) = .ok value at evaluated
        exact scalarCastView_canonical ctx (.uint (leftMaximum * rightMaximum))
          (leftValue * rightValue) value modulus evaluated
  | cast target source ihSource =>
    rename_i sourceTy
    cases sourceEval : source.eval ctx env with
    | error message =>
      simp [Expr.eval, sourceEval, bind, Bind.bind, Except.bind] at evaluated
    | ok sourceValue =>
      simp only [Expr.eval, sourceEval, bind, Bind.bind, Except.bind] at evaluated
      change scalarCastView ctx target (ScalarNormalization.number sourceTy sourceValue) =
        .ok value at evaluated
      exact scalarCastView_canonical ctx target
        (ScalarNormalization.number sourceTy sourceValue) value modulus evaluated
  | letE name bound body ihBound ihBody =>
    rename_i sourceTy resultTy
    cases boundEval : bound.eval ctx env with
    | error message =>
      simp [Expr.eval, boundEval, bind, Bind.bind, Except.bind] at evaluated
    | ok boundValue =>
      simp only [Expr.eval, boundEval, bind, Bind.bind, Except.bind] at evaluated
      exact ihBody ((name, Value.pack sourceTy boundValue) :: env) value evaluated
  | assertE condition body ihCondition ihBody =>
    cases conditionEval : condition.eval ctx env with
    | error message =>
      simp [Expr.eval, conditionEval, bind, Bind.bind, Except.bind] at evaluated
    | ok conditionValue =>
      cases conditionValue with
      | false =>
        simp [Expr.eval, conditionEval, bind, Bind.bind, Except.bind] at evaluated
      | true =>
        simp only [Expr.eval, conditionEval, bind, Bind.bind, Except.bind] at evaluated
        exact ihBody env value evaluated
  | disclose span source ihSource =>
    apply ihSource env value
    simpa [Expr.eval] using evaluated
  | eq left right ihLeft ihRight =>
    cases value <;> simp [Canonical, ScalarNormalization.number, Field.modulus]
  | select condition yes no ihCondition ihYes ihNo =>
    cases conditionEval : condition.eval ctx env with
    | error message =>
      simp [Expr.eval, conditionEval, bind, Bind.bind, Except.bind] at evaluated
    | ok conditionValue =>
      cases yesEval : yes.eval ctx env with
      | error message =>
        simp [Expr.eval, conditionEval, yesEval, bind, Bind.bind, Except.bind] at evaluated
      | ok yesValue =>
        cases noEval : no.eval ctx env with
        | error message =>
          simp [Expr.eval, conditionEval, yesEval, noEval, bind, Bind.bind,
            Except.bind] at evaluated
        | ok noValue =>
          simp [Expr.eval, conditionEval, yesEval, noEval, bind, Bind.bind,
            Except.bind] at evaluated
          change Except.ok (if conditionValue = true then yesValue else noValue) =
            Except.ok value at evaluated
          have selectedEq : (if conditionValue = true then yesValue else noValue) = value :=
            Except.ok.inj evaluated
          cases conditionValue with
          | false =>
            rw [← selectedEq]
            exact ihNo env noValue noEval
          | true =>
            rw [← selectedEq]
            exact ihYes env yesValue yesEval
  | poseidon2 domain left right ihLeft ihRight =>
    have domainNotGe : ¬ ctx.modulus ≤ domain := by
      by_cases invalid : ctx.modulus ≤ domain
      · simp [Expr.eval, invalid, bind, Bind.bind, Except.bind] at evaluated
      · exact invalid
    cases leftEval : left.eval ctx env with
    | error message =>
      simp [Expr.eval, domainNotGe, leftEval, bind, Bind.bind, Except.bind] at evaluated
    | ok leftValue =>
      cases rightEval : right.eval ctx env with
      | error message =>
        simp [Expr.eval, domainNotGe, leftEval, rightEval, bind, Bind.bind,
          Except.bind] at evaluated
      | ok rightValue =>
        cases oracleEval : ctx.poseidon2 domain leftValue rightValue with
        | error message =>
          simp [Expr.eval, domainNotGe, leftEval, rightEval, oracleEval, bind,
            Bind.bind, Except.bind] at evaluated
        | ok result =>
          have resultBound : result < ctx.modulus := by
            by_cases bound : result < ctx.modulus
            · exact bound
            · have invalid : ctx.modulus ≤ result := by omega
              simp [Expr.eval, domainNotGe, leftEval, rightEval,
                oracleEval, invalid, bind, Bind.bind, Except.bind] at evaluated
          have resultNotGe : ¬ ctx.modulus ≤ result := Nat.not_le_of_gt resultBound
          simp [Expr.eval, domainNotGe, leftEval, rightEval,
            oracleEval, resultNotGe, bind, Bind.bind, Except.bind] at evaluated
          change (Except.ok result : Except String Nat) = .ok value at evaluated
          have resultEq : result = value := Except.ok.inj evaluated
          subst value
          exact canonical_native_of_bound result (by simpa [modulus] using resultBound)

end Noctium.Verification.GenericStateEvaluationCanonical
