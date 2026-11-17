import Nightlean.IR

namespace Nightlean.Backend.Native

/-- Symbolic field computations used to compare typed source bindings with
produced SSA operands. This is syntax equality, not an algebraic optimizer. -/
inductive Term where
  | constant (value : Nat)
  | input (identifier : String)
  | unary (opcode : String) (value : Term)
  | binary (opcode : String) (left right : Term)
  | select (condition yes no : Term)
  | hash (values : List Term)
  deriving Repr, Inhabited

/- Structural equality is total so acceptance checks have kernel-visible meaning.
The comparison follows the same constructor, string and list order as derived BEq. -/
mutual
def Term.equal : Term → Term → Bool
  | .constant a, .constant b => a == b
  | .input a, .input b => a == b
  | .unary a x, .unary b y => a == b && Term.equal x y
  | .binary a x y, .binary b z w => a == b && Term.equal x z && Term.equal y w
  | .select c x y, .select d z w => Term.equal c d && Term.equal x z && Term.equal y w
  | .hash xs, .hash ys => Term.equalList xs ys
  | _, _ => false
termination_by left right => sizeOf left + sizeOf right

def Term.equalList : List Term → List Term → Bool
  | [], [] => true
  | x :: xs, y :: ys => Term.equal x y && Term.equalList xs ys
  | _, _ => false
termination_by left right => sizeOf left + sizeOf right
end
mutual
theorem Term.equal_iff : (left right : Term) → Term.equal left right = true ↔ left = right
  | .constant a, .constant b => by simp [Term.equal]
  | .input a, .input b => by simp [Term.equal]
  | .unary a x, .unary b y => by simp [Term.equal, Term.equal_iff x y]
  | .binary a x y, .binary b z w => by simp [Term.equal, Term.equal_iff x z, Term.equal_iff y w, and_assoc]
  | .select c x y, .select d z w => by simp [Term.equal, Term.equal_iff c d, Term.equal_iff x z, Term.equal_iff y w, and_assoc]
  | .hash xs, .hash ys => by simp [Term.equal, Term.equalList_iff xs ys]
  | .constant _, .input _ | .constant _, .unary .. | .constant _, .binary .. | .constant _, .select .. | .constant _, .hash _
  | .input _, .constant _ | .input _, .unary .. | .input _, .binary .. | .input _, .select .. | .input _, .hash _
  | .unary .., .constant _ | .unary .., .input _ | .unary .., .binary .. | .unary .., .select .. | .unary .., .hash _
  | .binary .., .constant _ | .binary .., .input _ | .binary .., .unary .. | .binary .., .select .. | .binary .., .hash _
  | .select .., .constant _ | .select .., .input _ | .select .., .unary .. | .select .., .binary .. | .select .., .hash _
  | .hash _, .constant _ | .hash _, .input _ | .hash _, .unary .. | .hash _, .binary .. | .hash _, .select .. => by simp [Term.equal]
termination_by left right => sizeOf left + sizeOf right

theorem Term.equalList_iff : (left right : List Term) → Term.equalList left right = true ↔ left = right
  | [], [] => by simp [Term.equalList]
  | x :: xs, y :: ys => by simp [Term.equalList, Term.equal_iff x y, Term.equalList_iff xs ys]
  | [], _ :: _ | _ :: _, [] => by simp [Term.equalList]
termination_by left right => sizeOf left + sizeOf right
end

instance : BEq Term := ⟨Term.equal⟩

instance : LawfulBEq Term where
  eq_of_beq := fun h => (Term.equal_iff _ _).mp h
  rfl := (Term.equal_iff _ _).mpr rfl

abbrev AliasEnvironment := List (String × Term)

structure Normalized where
  term : Term
  bounds : List (Term × Nat) := []
  assertions : List Term := []

private def requireSourceType (ty : Ty) (term : Term) (bounds : List (Term × Nat)) : Normalized :=
  {term, bounds := match ty with
    | .native => bounds
    | .bool => bounds ++ [(term, 1)]
    | .uint maximum => bounds ++ [(term, maximum)]}

private def arithmetic (ty : Ty) (opcode : String) (left right : Normalized) : Normalized :=
  {requireSourceType ty (.binary opcode left.term right.term) (left.bounds ++ right.bounds) with assertions := left.assertions ++ right.assertions}

private def subtraction (ty : Ty) (left right : Normalized) : Normalized :=
  {requireSourceType ty (.binary "add" left.term (.unary "neg" right.term)) (left.bounds ++ right.bounds) with assertions := left.assertions ++ right.assertions}

/-- Public reduction equations for proof modules. The producer uses the same helpers. -/
theorem requireSourceType_eq (ty : Ty) (term : Term) (bounds : List (Term × Nat)) :
    requireSourceType ty term bounds =
      {term, bounds := match ty with
        | .native => bounds
        | .bool => bounds ++ [(term, 1)]
        | .uint maximum => bounds ++ [(term, maximum)]} := rfl

theorem arithmetic_eq (ty : Ty) (opcode : String) (left right : Normalized) :
    arithmetic ty opcode left right =
      {requireSourceType ty (.binary opcode left.term right.term) (left.bounds ++ right.bounds)
        with assertions := left.assertions ++ right.assertions} := rfl

theorem subtraction_eq (ty : Ty) (left right : Normalized) :
    subtraction ty left right =
      {requireSourceType ty (.binary "add" left.term (.unary "neg" right.term))
        (left.bounds ++ right.bounds) with assertions := left.assertions ++ right.assertions} := rfl

def normalize (env : AliasEnvironment) : (value : Expr ty) → Except String Normalized
  | .native value => pure {term := .constant value}
  | .bool value => pure (requireSourceType .bool (.constant (if value then 1 else 0)) [])
  | .uint maximum value => pure (requireSourceType (.uint maximum) (.constant value) [])
  | .ref name => do
    let some term := env.lookup name | throw s!"unbound native source symbol '{name}'"
    pure (requireSourceType ty term [])
  | .add left right => do pure (arithmetic ty "add" (← normalize env left) (← normalize env right))
  | .mul left right => do pure (arithmetic ty "mul" (← normalize env left) (← normalize env right))
  | .sub left right => do pure (subtraction ty (← normalize env left) (← normalize env right))
  | .uadd left right => do pure (arithmetic ty "add" (← normalize env left) (← normalize env right))
  | .umul left right => do pure (arithmetic ty "mul" (← normalize env left) (← normalize env right))
  | .usub left right => do pure (subtraction ty (← normalize env left) (← normalize env right))
  | .eq left right => do pure (arithmetic ty "test_eq" (← normalize env left) (← normalize env right))
  | .cast target value => do
    let value ← normalize env value
    let term := match target with
      | .bool => .unary "not" (.binary "test_eq" value.term (.constant 0))
      | _ => value.term
    pure {requireSourceType target term value.bounds with assertions := value.assertions}
  | .letE name value body => do
    let value ← normalize env value
    let body ← normalize ((name, value.term) :: env) body
    pure {body with bounds := value.bounds ++ body.bounds, assertions := value.assertions ++ body.assertions}
  | .assertE condition body => do
    let condition ← normalize env condition
    let body ← normalize env body
    pure {body with
      bounds := condition.bounds ++ body.bounds
      assertions := condition.assertions ++ [condition.term] ++ body.assertions}
  | .disclose _ value => normalize env value
  | .select condition yes no => do
    let condition ← normalize env condition
    let yes ← normalize env yes
    let no ← normalize env no
    pure {requireSourceType ty (.select condition.term yes.term no.term)
      (condition.bounds ++ yes.bounds ++ no.bounds) with
      assertions := condition.assertions ++ yes.assertions ++ no.assertions}
  | .poseidon2 domain left right => do
    let left ← normalize env left
    let right ← normalize env right
    pure {term := .hash [.constant domain, left.term, right.term], bounds := left.bounds ++ right.bounds, assertions := left.assertions ++ right.assertions}

structure InputRequirement where
  identifier : String
  visibility : Visibility
  ty : Ty
  /-- Conditional transcript consumption is allowed only for source-bound public reads. -/
  activityGuard : Option Term := none
  deriving Repr

inductive ProducerMode where
  | relation | ledgerCall
  deriving Repr, BEq, DecidableEq

/-- Trusted expected statement derived from an already validated/disclosure-
checked typed program. Raw callers do not gain authorization by inventing it. -/
structure Expected where
  mode : ProducerMode
  inputs : List InputRequirement
  groups : List (List Term)
  /-- Exact source-derived Impact guard per group. Empty preserves all-active
  relations produced before activity guards were introduced. -/
  groupGuards : List Term := []
  returns : List Term
  assertions : List Term
  bounds : List (Term × Nat)
  deriving Repr

theorem normalize_disclosure_erasure (env : AliasEnvironment) (span : SourceSpan) (value : Expr ty) :
    normalize env (.disclose span value) = normalize env value := by rfl

end Nightlean.Backend.Native
