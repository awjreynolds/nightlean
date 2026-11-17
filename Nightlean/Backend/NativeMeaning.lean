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
  | bytes (values : List Term)
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
  | .bytes xs, .bytes ys => Term.equalList xs ys
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
  | .bytes xs, .bytes ys => by simp [Term.equal, Term.equalList_iff xs ys]
  | .constant _, .input _ | .constant _, .unary .. | .constant _, .binary .. | .constant _, .select .. | .constant _, .hash _ | .constant _, .bytes _
  | .input _, .constant _ | .input _, .unary .. | .input _, .binary .. | .input _, .select .. | .input _, .hash _ | .input _, .bytes _
  | .unary .., .constant _ | .unary .., .input _ | .unary .., .binary .. | .unary .., .select .. | .unary .., .hash _ | .unary .., .bytes _
  | .binary .., .constant _ | .binary .., .input _ | .binary .., .unary .. | .binary .., .select .. | .binary .., .hash _ | .binary .., .bytes _
  | .select .., .constant _ | .select .., .input _ | .select .., .unary .. | .select .., .binary .. | .select .., .hash _ | .select .., .bytes _
  | .hash _, .constant _ | .hash _, .input _ | .hash _, .unary .. | .hash _, .binary .. | .hash _, .select .. | .hash _, .bytes _
  | .bytes _, .constant _ | .bytes _, .input _ | .bytes _, .unary .. | .bytes _, .binary .. | .bytes _, .select .. | .bytes _, .hash _ => by simp [Term.equal]
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
    | .uint maximum => bounds ++ [(term, maximum)]
    | .bytes _ => bounds}

def packByteTerms : List Term → Term
  | [] => .constant 0
  | byte :: rest => .binary "add" byte (.binary "mul" (.constant 256) (packByteTerms rest))

/-- Canonical typed source term for persistent_hash(Bytes32). The operands are
the exact FAB-aligned fields: the high byte, then the packed low 31 bytes. -/
def persistentHash32Term (highByte low31 : Term) : Term :=
  .unary "persistent_hash32" (.bytes [highByte, low31])

/-- Modern Encode output chunk terms. Index 0 is low31 and index 1 is highByte. -/
def encodedHashChunkTerm (digest : Term) (index : Nat) : Term :=
  .unary (if index == 0 then "encode_bytes32_low31" else "encode_bytes32_highByte") digest

private def bytesFieldTerms (terms : List Term) (index : Nat) : Except String (List Term) := do
  if terms.length != 32 then throw "Bytes32 source term has wrong byte count"
  match index with
  | 0 => pure (terms.drop 31)
  | 1 => pure (terms.take 31)
  | _ => throw "Bytes32 field chunk index is out of range"

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
        | .uint maximum => bounds ++ [(term, maximum)]
        | .bytes _ => bounds} := rfl

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
  | .bytesField value index => do
    let normalized ← normalize env value
    match normalized.term with
    | .unary "persistent_hash32" _ =>
      match index with
      | 0 =>
        let term := encodedHashChunkTerm normalized.term 1
        pure {term := term, bounds := normalized.bounds, assertions := normalized.assertions}
      | 1 =>
        let term := encodedHashChunkTerm normalized.term 0
        pure {term := term, bounds := normalized.bounds, assertions := normalized.assertions}
      | _ => throw "Bytes32 field chunk index is out of range"
    | .bytes terms => do
      let chunk ← bytesFieldTerms terms index
      let term := packByteTerms chunk
      pure {term := term, bounds := normalized.bounds, assertions := normalized.assertions}
    | _ => throw "Bytes32 normalization lost byte identity"
  | .bytesAt value index => do
    let normalized ← normalize env value
    match normalized.term with
    | .unary "persistent_hash32" _ => throw "byteAt on a computed persistentHash32 digest is unsupported"
    | .bytes terms => do
      let some term := terms[index]? | throw "Bytes32 byte index is out of range"
      pure {term := term, bounds := normalized.bounds ++ [(term, 255)], assertions := normalized.assertions}
    | _ => throw "Bytes32 normalization lost byte identity"
  | .persistentHash32 value => do
    let normalized ← normalize env value
    let (highByte, low31) ← match normalized.term with
      | .bytes terms => do
        unless terms.length == 32 do throw "Bytes32 source term has wrong byte count"
        let some high := terms[31]? | throw "Bytes32 source term has no high byte"
        let low ← bytesFieldTerms terms 1
        pure (high, packByteTerms low)
      | .unary "persistent_hash32" _ =>
        pure (encodedHashChunkTerm normalized.term 1, encodedHashChunkTerm normalized.term 0)
      | _ => throw "persistentHash32 source lost Bytes32 identity"
    let term := persistentHash32Term highByte low31
    pure {term, bounds := normalized.bounds, assertions := normalized.assertions}
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

def InputRequirement.byte (input : Input) (index : Nat) : InputRequirement :=
  {identifier := input.nativeIdentifiers[index]!, visibility := input.visibility, ty := .uint 255}

def Input.requirements (input : Input) : List InputRequirement :=
  match input.ty with
  | .bytes length => (List.range length).map (InputRequirement.byte input)
  | _ => [{identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}]

def Input.sourceTerm (input : Input) : Term :=
  match input.ty with
  | .bytes _ => .bytes (input.nativeIdentifiers.map Term.input)
  | _ => .input ("%input_" ++ input.name)

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
    normalize env (.disclose span value) = normalize env value := by
  rw [normalize.eq_18]

end Nightlean.Backend.Native
