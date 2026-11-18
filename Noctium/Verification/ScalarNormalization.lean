import Noctium.Backend.NativeExpected
import Noctium.Verification.NativeRelation

namespace Noctium.Verification.ScalarNormalization

open Backend.Native NativeRelation

/-- The symbolic terms already used by the mandatory producer validator have a
field interpretation independent of SSA names, allocation and CSE. -/
def interpret (hash : Hash) (inputs : Assignment) : Term → Scalar
  | .constant value => scalar value
  | .input name => inputs name
  | .unary opcode value =>
    let value := interpret hash inputs value
    if opcode == "neg" then scalar (Field.modulus - value.val)
    else if opcode == "not" then bit (decide (value = zero))
    else zero
  | .binary opcode left right =>
    let left := interpret hash inputs left
    let right := interpret hash inputs right
    if opcode == "add" then scalar (left.val + right.val)
    else if opcode == "mul" then scalar (left.val * right.val)
    else if opcode == "test_eq" then bit (decide (left = right))
    else if opcode.startsWith "less_than:" then bit (decide (left.val < right.val))
    else zero
  | .select condition yes no =>
    if interpret hash inputs condition = one then interpret hash inputs yes
    else interpret hash inputs no
  | .hash values => hash (values.map (interpret hash inputs))

/-- Source numeric representations, before any modular reduction. -/
def number : (ty : Ty) → ty.Denote → Nat
  | .native, value | .uint _, value => value
  | .bool, value => if value then 1 else 0

/-- A scalar source value has its declared range and canonical encoding. -/
def Canonical (ty : Ty) (value : ty.Denote) : Prop :=
  number ty value < Field.modulus ∧ match ty with
    | .native => True
    | .bool => True
    | .uint maximum => maximum ≤ ScalarPolicy.maxUint ∧ value ≤ maximum

/-- Bounds include partial operations whose results are discarded by a let or
an eager select. Assertions stay in source traversal order. -/
def Requirements (hash : Hash) (inputs : Assignment) (normalized : Normalized) : Prop :=
  (∀ requirement ∈ normalized.bounds, (interpret hash inputs requirement.1).val ≤ requirement.2) ∧
  (∀ term ∈ normalized.assertions, interpret hash inputs term = one)

/-- All aliases, including a shadowing let alias, refer to the first visible
binding. Every numeric value is canonical before the alias is used. -/
def AliasAgreement (hash : Hash) (inputs : Assignment) (aliases : AliasEnvironment)
    (values : EvalEnv) : Prop :=
  ∀ name ty raw value, values.lookup name = some raw → raw.as ty = some value →
    Canonical ty value ∧ ∃ term, aliases.lookup name = some term ∧
      interpret hash inputs term = scalar (number ty value)

/-- Observable normal-form meaning. This is intentionally independent of an
honest SSA witness: `inputs` fixes only the declared source values. -/
def Represents (hash : Hash) (inputs : Assignment) (ty : Ty)
    (normalized : Normalized) (value : ty.Denote) : Prop :=
  Canonical ty value ∧ Requirements hash inputs normalized ∧
    interpret hash inputs normalized.term = scalar (number ty value)

@[simp] theorem number_pack_as (ty : Ty) (value : ty.Denote) :
    (Value.pack ty value).as ty = some value := by
  cases ty <;> simp [Value.pack, Value.as]

@[simp] theorem number_bool (value : Bool) : number .bool value = if value then 1 else 0 := rfl

@[simp] theorem interpret_constant (hash : Hash) (inputs : Assignment) (value : Nat) :
    interpret hash inputs (.constant value) = scalar value := by simp [interpret]

@[simp] theorem interpret_input (hash : Hash) (inputs : Assignment) (name : String) :
    interpret hash inputs (.input name) = inputs name := by simp [interpret]

/-- The semantic environment extends in the same order as the actual normalizer.
No global name-uniqueness assumption forbids valid let shadowing. -/
theorem aliasAgreement_cons (hash : Hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv) (name : String) (ty : Ty)
    (value : ty.Denote) (term : Term)
    (agreement : AliasAgreement hash inputs aliases values)
    (canonical : Canonical ty value)
    (meaning : interpret hash inputs term = scalar (number ty value)) :
    AliasAgreement hash inputs ((name, term) :: aliases) ((name, Value.pack ty value) :: values) := by
  intro found foundTy raw foundValue lookup typed
  by_cases same : found = name
  · subst found
    simp only [List.lookup_cons, beq_self_eq_true] at lookup
    cases lookup
    cases ty <;> cases foundTy <;> simp_all [Value.pack, Value.as, Canonical, number]
  · have unequal : (found == name) = false := by simp [same]
    simp only [List.lookup_cons, unequal] at lookup
    obtain ⟨canonical, existing, lookup, meaning⟩ := agreement found foundTy raw foundValue lookup typed
    exact ⟨canonical, existing, by simp [List.lookup_cons, unequal, lookup], meaning⟩

end Noctium.Verification.ScalarNormalization

namespace Noctium.Verification.ScalarNormalization
open Backend.Native NativeRelation

private theorem requirements_empty (hash : Hash) (inputs : Assignment) (term : Term) :
    Requirements hash inputs {term := term} := by simp [Requirements]

private theorem bit_number (b : Bool) : bit b = scalar (number .bool b) := by
  cases b <;> apply Fin.ext <;> decide

@[simp] theorem interpret_add (hash : Hash) (inputs : Assignment) (left right : Term) :
    interpret hash inputs (.binary "add" left right) =
      scalar ((interpret hash inputs left).val + (interpret hash inputs right).val) := by
  simp [interpret]

@[simp] theorem interpret_mul (hash : Hash) (inputs : Assignment) (left right : Term) :
    interpret hash inputs (.binary "mul" left right) =
      scalar ((interpret hash inputs left).val * (interpret hash inputs right).val) := by
  simp [interpret]

@[simp] theorem interpret_neg (hash : Hash) (inputs : Assignment) (value : Term) :
    interpret hash inputs (.unary "neg" value) = scalar (Field.modulus - (interpret hash inputs value).val) := by
  simp [interpret]

@[simp] theorem scalar_zero : scalar 0 = zero := by apply Fin.ext; rfl
@[simp] theorem scalar_one : scalar 1 = one := by apply Fin.ext; decide

private theorem scalar_eq_zero (value : Nat) (bound : value < Field.modulus) :
    scalar value = zero ↔ value = 0 := by
  constructor
  · intro equality
    have raw := congrArg Fin.val equality
    simpa [scalar, zero, Nat.mod_eq_of_lt bound] using raw
  · intro equality
    subst value
    exact scalar_zero

@[simp] theorem interpret_testEq (hash : Hash) (inputs : Assignment) (left right : Term) :
    interpret hash inputs (.binary "test_eq" left right) =
      bit (decide (interpret hash inputs left = interpret hash inputs right)) := by
  simp [interpret]

@[simp] theorem interpret_not (hash : Hash) (inputs : Assignment) (value : Term) :
    interpret hash inputs (.unary "not" value) = bit (decide (interpret hash inputs value = zero)) := by
  simp [interpret]

private theorem scalar_numbers_equal (ty : Ty) (left right : ty.Denote)
    (hl : Canonical ty left) (hr : Canonical ty right) :
    scalar (number ty left) = scalar (number ty right) ↔ number ty left = number ty right := by
  constructor
  · intro equality
    have raw := congrArg Fin.val equality
    simpa only [scalar, Nat.mod_eq_of_lt hl.1, Nat.mod_eq_of_lt hr.1] using raw
  · exact congrArg scalar

private theorem bool_canonical (value : Bool) : Canonical .bool value := by
  cases value <;> exact ⟨by decide, trivial⟩

@[simp] theorem interpret_select (hash : Hash) (inputs : Assignment) (condition yes no : Term) :
    interpret hash inputs (.select condition yes no) =
      if interpret hash inputs condition = one then interpret hash inputs yes else interpret hash inputs no := by
  simp [interpret]

@[simp] theorem interpret_hash (hash : Hash) (inputs : Assignment) (values : List Term) :
    interpret hash inputs (.hash values) = hash (values.map (interpret hash inputs)) := by
  simp [interpret]

theorem subtraction_mod (a b : Nat) (hb : b < Field.modulus) :
    scalar (a + (scalar (Field.modulus - b)).val) = scalar ((Field.modulus + a - b) % Field.modulus) := by
  apply Fin.ext
  change (a + (Field.modulus - b) % Field.modulus) % Field.modulus =
    ((Field.modulus + a - b) % Field.modulus) % Field.modulus
  rw [Nat.mod_mod, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  congr 1
  omega

private theorem requirements_join (hash : Hash) (inputs : Assignment)
    (left right : Normalized) (term : Term)
    (hl : Requirements hash inputs left) (hr : Requirements hash inputs right) :
    Requirements hash inputs {term := term, bounds := left.bounds ++ right.bounds, assertions := left.assertions ++ right.assertions} := by
  constructor
  · intro requirement member
    rcases List.mem_append.mp member with member | member
    · exact hl.1 requirement member
    · exact hr.1 requirement member
  · intro value member
    rcases List.mem_append.mp member with member | member
    · exact hl.2 value member
    · exact hr.2 value member

private def typeBounds (ty : Ty) (term : Term) (bounds : List (Term × Nat)) : List (Term × Nat) :=
  match ty with
  | .native => bounds
  | .bool => bounds ++ [(term, 1)]
  | .uint maximum => bounds ++ [(term, maximum)]

private theorem represent_with_bound (hash : Hash) (inputs : Assignment) (ty : Ty)
    (term : Term) (bounds : List (Term × Nat)) (assertions : List Term)
    (value : ty.Denote) (canonical : Canonical ty value)
    (requirements : Requirements hash inputs {term, bounds, assertions})
    (meaning : interpret hash inputs term = scalar (number ty value)) :
    Represents hash inputs ty {term, assertions, bounds := typeBounds ty term bounds} value := by
  refine ⟨canonical, ?_, meaning⟩
  constructor
  · intro requirement member
    cases ty with
    | native => exact requirements.1 requirement member
    | bool =>
      rcases List.mem_append.mp member with member | member
      · exact requirements.1 requirement member
      · have same := List.mem_singleton.mp member
        subst requirement
        cases value <;> simp [meaning, number, scalar, Field.modulus]
    | uint maximum =>
      rcases List.mem_append.mp member with member | member
      · exact requirements.1 requirement member
      · have same := List.mem_singleton.mp member
        subst requirement
        rw [meaning]
        change value % Field.modulus ≤ maximum
        rw [Nat.mod_eq_of_lt (show value < Field.modulus from canonical.1)]
        exact canonical.2.2
  · exact requirements.2

/-- Successful source evaluation establishes every range and assertion retained
by normalization, including unused partial computations and both select arms. -/
theorem normalize_success (ctx : EvalContext) (hash : Hash)
    (implementation : HashAgreement ctx hash) (inputs : Assignment)
    (aliases : AliasEnvironment) (values : EvalEnv)
    (agreement : AliasAgreement hash inputs aliases values)
    (expression : Expr ty) (value : ty.Denote)
    (success : expression.eval ctx values = .ok value) :
    ∃ normalized, normalize aliases expression = .ok normalized ∧
      Represents hash inputs ty normalized value := by
  induction expression generalizing aliases values with
  | native n =>
    simp only [Expr.eval] at success
    split at success
    next h =>
      cases success
      refine ⟨{term := .constant n}, rfl, ⟨?_, requirements_empty _ _ _, by simp [number]⟩⟩
      exact ⟨by simpa [number, implementation.modulus] using h, trivial⟩
    next h => cases success
  | bool b =>
    cases success
    refine ⟨_, rfl, ?_⟩
    simp only [requireSourceType_eq]
    cases b <;> unfold Represents Canonical number
    all_goals simp only [Bool.false_eq_true, ↓reduceIte, and_true]
    all_goals refine ⟨by decide, ?_, by simp⟩
    all_goals simp [Requirements, scalar, Field.modulus]
  | uint maximum n =>
    simp only [Expr.eval] at success
    split at success
    next h =>
      cases success
      refine ⟨_, rfl, ?_⟩
      change (maximum ≤ ScalarPolicy.maxUint && n ≤ maximum && n < ctx.modulus) = true at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨hmaximum, hvalue⟩, hfield⟩
      simp [Represents, Canonical, number, Requirements, requireSourceType_eq,
        scalar, Nat.mod_eq_of_lt (show n < Field.modulus by simpa [implementation.modulus] using hfield), hmaximum, hvalue,
        show n < Field.modulus by simpa [implementation.modulus] using hfield]
    next h => cases success
  | @ref ty name =>
    simp only [Expr.eval] at success
    cases lookup : values.lookup name with
    | none => simp [lookup] at success
    | some raw =>
      simp only [lookup] at success
      cases typed : raw.as ty with
      | none => simp [typed] at success
      | some result =>
        simp only [typed] at success
        split at success
        next h => cases success
        next h =>
          cases success
          obtain ⟨canonical, term, alias, meaning⟩ := agreement name ty raw value lookup typed
          refine ⟨_, by simp only [normalize, alias]; rfl, ?_⟩
          simp only [requireSourceType_eq]
          refine ⟨canonical, ?_, meaning⟩
          cases ty with
          | native => simp [Requirements]
          | bool => cases value <;> simp [Requirements, meaning, number, scalar, Field.modulus]
          | uint maximum =>
            have bound : (scalar (number (.uint maximum) value)).val ≤ maximum := by
              change value % Field.modulus ≤ maximum
              rw [Nat.mod_eq_of_lt (show value < Field.modulus from canonical.1)]
              exact canonical.2.2
            simpa [Requirements, meaning] using bound
  | add a b ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, implementation.modulus, Field.modulus, bind, pure, Except.bind, Except.map, Except.pure] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, pure, Except.bind, Except.map, Except.pure] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, pure, Except.bind, Except.map, Except.pure] at success
        cases success
        refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
        simp only [arithmetic_eq, requireSourceType_eq]
        refine ⟨⟨Nat.mod_lt _ (by decide), trivial⟩, requirements_join _ _ _ _ _ ar br, ?_⟩
        simp only [interpret_add, am, bm]
        change scalar ((av % Field.modulus) + (bv % Field.modulus)) = scalar ((av + bv) % Field.modulus)
        simp [scalar, Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
          Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)]
  | mul a b ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, implementation.modulus, Field.modulus, bind, pure, Except.bind, Except.map, Except.pure] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, pure, Except.bind, Except.map, Except.pure] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, pure, Except.bind, Except.map, Except.pure] at success
        cases success
        refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
        simp only [arithmetic_eq, requireSourceType_eq]
        refine ⟨⟨Nat.mod_lt _ (by decide), trivial⟩, requirements_join _ _ _ _ _ ar br, ?_⟩
        simp only [interpret_mul, am, bm]
        change scalar ((av % Field.modulus) * (bv % Field.modulus)) = scalar ((av * bv) % Field.modulus)
        simp [scalar, Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
          Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)]
  | sub a b ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, implementation.modulus, Field.modulus, bind, Except.bind, Except.pure] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, Except.bind, Except.pure] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp [Expr.eval, ea, eb, implementation.modulus, Field.modulus, bind, Except.bind, Except.pure] at success
        cases success
        refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
        simp only [subtraction_eq, requireSourceType_eq]
        refine ⟨⟨Nat.mod_lt _ (by decide), trivial⟩, requirements_join _ _ _ _ _ ar br, ?_⟩
        simp only [interpret_add, interpret_neg, am, bm]
        change scalar ((av % Field.modulus) + (scalar (Field.modulus - bv % Field.modulus)).val) =
          scalar ((Field.modulus + av - bv) % Field.modulus)
        rw [Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
          Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)]
        exact subtraction_mod av bv bc.1
  | @ uadd m n a b ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, bind, Except.bind] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, bind, Except.bind] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp only [Expr.eval, ea, eb, bind, Except.bind] at success
        change (if m + n ≤ ScalarPolicy.maxUint && av + bv ≤ m + n && av + bv < ctx.modulus
          then Except.ok (av + bv) else Except.error "scalar conversion exceeds unsigned bound") = Except.ok value at success
        split at success
        next valid =>
          cases success
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          have canonical : Canonical (.uint (m + n)) (av + bv) :=
            ⟨by simpa [implementation.modulus, number] using valid.2, valid.1.1, valid.1.2⟩
          refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
          simp only [arithmetic_eq, requireSourceType_eq]
          apply represent_with_bound _ _ _ _ _ _ _ canonical (requirements_join _ _ _ _ _ ar br)
          simp only [interpret_add, am, bm]
          change scalar ((av % Field.modulus) + (bv % Field.modulus)) = scalar (av + bv)
          rw [Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
            Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)]
        next invalid => cases success
  | @usub m n a b ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, bind, Except.bind] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, bind, Except.bind] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp only [Expr.eval, ea, eb, bind, Except.bind] at success
        by_cases underflow : av < bv
        · simp [underflow] at success
        · simp only [underflow, ↓reduceIte] at success
          change (if m ≤ ScalarPolicy.maxUint && av - bv ≤ m && av - bv < ctx.modulus
            then Except.ok (av - bv) else Except.error "scalar conversion exceeds unsigned bound") = Except.ok value at success
          split at success
          next valid =>
            cases success
            simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
            have canonical : Canonical (.uint m) (av - bv) :=
              ⟨by simpa [implementation.modulus, number] using valid.2, valid.1.1, valid.1.2⟩
            refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
            simp only [subtraction_eq, requireSourceType_eq]
            apply represent_with_bound _ _ _ _ _ _ _ canonical (requirements_join _ _ _ _ _ ar br)
            simp only [interpret_add, interpret_neg, am, bm]
            change scalar ((av % Field.modulus) + (scalar (Field.modulus - bv % Field.modulus)).val) = scalar (av - bv)
            rw [Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
              Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1), subtraction_mod av bv bc.1]
            have equality : Field.modulus + av - bv = Field.modulus + (av - bv) := Nat.add_sub_assoc (Nat.le_of_not_gt underflow) _
            rw [equality, Nat.add_mod]
            simp only [Nat.mod_self, Nat.zero_add, Nat.mod_mod]
            rw [Nat.mod_eq_of_lt (show av - bv < Field.modulus from canonical.1)]
          next invalid => cases success
  | @ umul m n a b ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, bind, Except.bind] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, bind, Except.bind] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp only [Expr.eval, ea, eb, bind, Except.bind] at success
        change (if m * n ≤ ScalarPolicy.maxUint && av * bv ≤ m * n && av * bv < ctx.modulus
          then Except.ok (av * bv) else Except.error "scalar conversion exceeds unsigned bound") = Except.ok value at success
        split at success
        next valid =>
          cases success
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          have canonical : Canonical (.uint (m * n)) (av * bv) :=
            ⟨by simpa [implementation.modulus, number] using valid.2, valid.1.1, valid.1.2⟩
          refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
          simp only [arithmetic_eq, requireSourceType_eq]
          apply represent_with_bound _ _ _ _ _ _ _ canonical (requirements_join _ _ _ _ _ ar br)
          simp only [interpret_mul, am, bm]
          change scalar ((av % Field.modulus) * (bv % Field.modulus)) = scalar (av * bv)
          rw [Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
            Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)]
        next invalid => cases success
  | @cast source target expression ih =>
    cases ev : expression.eval ctx values with
    | error message => simp [Expr.eval, ev, bind, Except.bind] at success
    | ok result =>
      obtain ⟨vn, nv, vc, vr, vm⟩ := ih aliases values agreement result ev
      cases target with
      | native =>
        simp only [Expr.eval, ev, bind, Except.bind] at success
        change (if number source result < ctx.modulus then Except.ok (number source result)
          else Except.error "noncanonical scalar conversion") = Except.ok value at success
        split at success
        next bound =>
          cases success
          refine ⟨_, by simp only [normalize, nv]; rfl, ⟨?_, trivial⟩, vr, vm⟩
          simpa [number, implementation.modulus] using bound
        next invalid => cases success
      | bool =>
        simp only [Expr.eval, ev, bind, Except.bind] at success
        change Except.ok (number source result != 0) = Except.ok value at success
        cases success
        refine ⟨_, by simp only [normalize, nv]; rfl, ?_⟩
        simp only [requireSourceType_eq]
        apply represent_with_bound _ _ _ _ _ _ _
        · cases number source result != 0 <;> exact ⟨by decide, trivial⟩
        · exact vr
        · simp only [interpret_not, interpret_testEq, vm, interpret_constant, scalar_zero]
          simp only [scalar_eq_zero _ vc.1]
          by_cases isZero : number source result = 0
          · simp [isZero, bit, zero_ne_one, Ne.symm zero_ne_one]
          · simp [isZero, bit, zero_ne_one, Ne.symm zero_ne_one]
      | uint maximum =>
        simp only [Expr.eval, ev, bind, Except.bind] at success
        change (if maximum ≤ ScalarPolicy.maxUint && number source result ≤ maximum && number source result < ctx.modulus
          then Except.ok (number source result) else Except.error "scalar conversion exceeds unsigned bound") = Except.ok value at success
        split at success
        next valid =>
          cases success
          simp only [Bool.and_eq_true, decide_eq_true_eq] at valid
          have canonical : Canonical (.uint maximum) (number source result) :=
            ⟨by simpa [implementation.modulus, number] using valid.2, valid.1.1, valid.1.2⟩
          refine ⟨_, by simp only [normalize, nv]; rfl, ?_⟩
          simp only [requireSourceType_eq]
          exact represent_with_bound _ _ _ _ _ _ _ canonical vr vm
        next invalid => cases success
  | @letE source ty name expression body iv ib =>
    cases ev : expression.eval ctx values with
    | error message => simp [Expr.eval, ev, bind, Except.bind] at success
    | ok result =>
      obtain ⟨vn, nv, vc, vr, vm⟩ := iv aliases values agreement result ev
      have bodySuccess : body.eval ctx ((name, Value.pack source result) :: values) = .ok value := by
        simpa only [Expr.eval, ev, bind, Except.bind] using success
      obtain ⟨bn, nb, bc, br, bm⟩ := ib ((name, vn.term) :: aliases) ((name, Value.pack source result) :: values)
        (aliasAgreement_cons _ _ _ _ _ _ _ _ agreement vc vm) value bodySuccess
      refine ⟨{term := bn.term, bounds := vn.bounds ++ bn.bounds, assertions := vn.assertions ++ bn.assertions}, by simp only [normalize, nv, bind, Except.bind, nb]; rfl, bc, ?_, bm⟩
      exact requirements_join _ _ vn bn bn.term vr br
  | assertE condition body ic ib =>
    cases ec : condition.eval ctx values with
    | error message => simp [Expr.eval, ec, bind, Except.bind] at success
    | ok result =>
      cases result with
      | false => simp [Expr.eval, ec, bind, Except.bind] at success
      | true =>
        obtain ⟨cn, nc, cc, cr, cm⟩ := ic aliases values agreement true ec
        have bodySuccess : body.eval ctx values = .ok value := by
          simpa only [Expr.eval, ec, bind, Except.bind, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, Except.pure] using success
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement value bodySuccess
        refine ⟨{term := bn.term, bounds := cn.bounds ++ bn.bounds, assertions := cn.assertions ++ [cn.term] ++ bn.assertions}, by simp only [normalize, nc, nb]; rfl, bc, ?_, bm⟩
        constructor
        · intro requirement member
          rcases List.mem_append.mp member with member | member
          · exact cr.1 requirement member
          · exact br.1 requirement member
        · intro term member
          rcases List.mem_append.mp member with member | member
          · rcases List.mem_append.mp member with member | member
            · exact cr.2 term member
            · have same := List.mem_singleton.mp member
              subst term
              simpa [number, scalar, one, Field.modulus] using cm
          · exact br.2 term member
  | disclose span expression ih =>
    exact ih aliases values agreement value success
  | @eq ty a b ia ib =>
    cases ea : a.eval ctx values with
    | error message => simp [Expr.eval, ea, bind, Except.bind] at success
    | ok av =>
      cases eb : b.eval ctx values with
      | error message => simp [Expr.eval, ea, eb, bind, Except.bind] at success
      | ok bv =>
        obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
        obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
        simp only [Expr.eval, ea, eb, bind, Except.bind] at success
        have same : value = (number ty av == number ty bv) := by
          cases ty with
          | native => exact (Except.ok.inj success).symm
          | uint maximum => exact (Except.ok.inj success).symm
          | bool => cases av <;> cases bv <;> exact (Except.ok.inj success).symm
        subst value
        refine ⟨_, by simp only [normalize, na, nb]; rfl, ?_⟩
        simp only [arithmetic_eq, requireSourceType_eq]
        apply represent_with_bound _ _ _ _ _ _ _ (bool_canonical _) (requirements_join _ _ _ _ _ ar br)
        simp only [interpret_testEq, am, bm, scalar_numbers_equal ty av bv ac bc]
        rw [← bit_number]
        congr 1
  | @select ty c a b ic ia ib =>
    cases ec : c.eval ctx values with
    | error message => simp [Expr.eval, ec, bind, Except.bind] at success
    | ok cv =>
      cases ea : a.eval ctx values with
      | error message => simp [Expr.eval, ec, ea, bind, Except.bind] at success
      | ok av =>
        cases eb : b.eval ctx values with
        | error message => simp [Expr.eval, ec, ea, eb, bind, Except.bind] at success
        | ok bv =>
          obtain ⟨cn, nc, cc, cr, cm⟩ := ic aliases values agreement cv ec
          obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
          obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
          have sourceResult : value = if cv then av else bv := by
            simpa [Expr.eval, ec, ea, eb, bind, Except.bind, pure, Except.pure] using success.symm
          subst value
          refine ⟨_, by simp only [normalize, nc, na, nb]; rfl, ?_⟩
          simp only [requireSourceType_eq]
          change Represents hash inputs ty {term := .select cn.term an.term bn.term, bounds := typeBounds ty (.select cn.term an.term bn.term) (cn.bounds ++ an.bounds ++ bn.bounds), assertions := cn.assertions ++ an.assertions ++ bn.assertions} (if cv then av else bv)
          apply represent_with_bound hash inputs ty (.select cn.term an.term bn.term)
            (cn.bounds ++ an.bounds ++ bn.bounds) (cn.assertions ++ an.assertions ++ bn.assertions) (if cv then av else bv)
          · cases cv
            · exact bc
            · exact ac
          · exact requirements_join _ _
              {term := an.term, bounds := cn.bounds ++ an.bounds, assertions := cn.assertions ++ an.assertions}
              bn _ (requirements_join _ _ cn an _ cr ar) br
          · cases cv <;> simp [interpret_select, cm, am, bm, number_bool, zero_ne_one]
  | poseidon2 domain a b ia ib =>
    simp only [Expr.eval] at success
    split at success
    next invalid => cases success
    next valid =>
      have domainBound : domain < Field.modulus := by
        have : domain < ctx.modulus := Nat.lt_of_not_ge valid
        simpa [implementation.modulus] using this
      cases ea : a.eval ctx values with
      | error message => simp [ea, bind, Except.bind] at success
      | ok av =>
        cases eb : b.eval ctx values with
        | error message => simp [ea, eb, bind, Except.bind] at success
        | ok bv =>
          obtain ⟨an, na, ac, ar, am⟩ := ia aliases values agreement av ea
          obtain ⟨bn, nb, bc, br, bm⟩ := ib aliases values agreement bv eb
          have oracle : ctx.poseidon2 domain av bv = .ok (hash [scalar domain, scalar av, scalar bv]).val := by
            simpa only [scalar, Nat.mod_eq_of_lt domainBound,
              Nat.mod_eq_of_lt (show av < Field.modulus from ac.1),
              Nat.mod_eq_of_lt (show bv < Field.modulus from bc.1)] using
              implementation.calls (scalar domain) (scalar av) (scalar bv)
          have resultBound : (hash [scalar domain, scalar av, scalar bv]).val < ctx.modulus := by
            simpa [implementation.modulus] using (hash [scalar domain, scalar av, scalar bv]).isLt
          simp [ea, eb, oracle, bind, Except.bind, pure, Except.pure,
            Nat.not_le_of_gt resultBound] at success
          cases success
          refine ⟨_, by simp only [normalize, na, nb]; rfl, ⟨(hash _).isLt, trivial⟩,
            requirements_join _ _ _ _ _ ar br, ?_⟩
          simp only [interpret_hash, List.map_cons, List.map_nil, interpret_constant, am, bm]
          change hash [scalar domain, scalar av, scalar bv] = scalar (hash [scalar domain, scalar av, scalar bv]).val
          apply Fin.ext
          exact (Nat.mod_eq_of_lt (hash [scalar domain, scalar av, scalar bv]).isLt).symm

end Noctium.Verification.ScalarNormalization
