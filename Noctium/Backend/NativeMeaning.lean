import Noctium.IR

namespace Noctium.Backend.Native

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
    | .bytes _ | .jubjubScalar | .jubjubPoint => bounds}

def packByteTerms : List Term → Term
  | [] => .constant 0
  | byte :: rest => .binary "add" byte (.binary "mul" (.constant 256) (packByteTerms rest))

/-- Canonical typed source term for persistent_hash(Bytes32). The operands are
the exact FAB-aligned fields: the high byte, then the packed low 31 bytes. -/
def persistentHash32Term (highByte low31 : Term) : Term :=
  .unary "persistent_hash32" (.bytes [highByte, low31])

/-- A one-element Bytes32 vector has the same FAB alignment as one Bytes32.
Larger vectors bind their element count and ordered aligned field pairs. -/
def persistentHashVector32Term (fields : List (Term × Term)) : Term :=
  match fields with
  | [field] => persistentHash32Term field.1 field.2
  | _ => .unary s!"persistent_hash_vector32:{fields.length}"
      (.hash (fields.flatMap fun (highByte, low31) => [highByte, low31]))

/-- Native persistent-hash consumes one canonical aligned field. -/
def persistentHashNativeTerm (value : Term) : Term :=
  .unary "persistent_hash_native" value

/-- Singleton Native vectors share the existing single-field term. Larger
vectors retain their arity and ordered field terms in the source relation. -/
def persistentHashNativeVectorTerm (values : List Term) : Term :=
  match values with
  | [value] => persistentHashNativeTerm value
  | _ => .unary s!"persistent_hash_native_vector:{values.length}" (.hash values)

/-- Distinct algorithms bind the fixed preimage length and ordered FAB chunks. -/
def fixedByteHashTerm (algorithm : String) (length : Nat) (alignedChunks : List Term) : Term :=
  .unary s!"{algorithm}_bytes:{length}" (.hash alignedChunks)

/-- Modern Encode output chunk terms. Index 0 is low31 and index 1 is highByte. -/
def encodedHashChunkTerm (digest : Term) (index : Nat) : Term :=
  .unary (if index == 0 then "encode_bytes32_low31" else "encode_bytes32_highByte") digest

private def bytesFieldTerms (terms : List Term) (index : Nat) : Except String (List Term) := do
  if terms.length != 32 then throw "Bytes32 source term has wrong byte count"
  match index with
  | 0 => pure (terms.drop 31)
  | 1 => pure (terms.take 31)
  | _ => throw "Bytes32 field chunk index is out of range"

private def opaqueBytes32Value : Term → Bool
  | .unary opcode _ => opcode == "persistent_hash32" || opcode == "persistent_hash_native" ||
      opcode.startsWith "persistent_hash_vector32:" || opcode.startsWith "persistent_hash_native_vector:" ||
      opcode.startsWith "to_bytes32_" || opcode.startsWith "from_bytes32_" ||
      opcode == "bytes32_from_chunks" || opcode == "reverse_bytes32"
      || opcode.startsWith "bytes_from_chunks:" || opcode.startsWith "reverse_bytes:"
      || opcode.startsWith "slice_bytes:"
      || opcode.startsWith "sha512_bytes:" || opcode.startsWith "keccak256_bytes:"
  | .binary opcode _ _ => opcode.startsWith "concat_bytes:"
  | _ => false

private def splitBytes32Fields : Term → Except String (Term × Term)
  | .bytes terms => do
    unless terms.length == 32 do throw "Bytes32 source term has wrong byte count"
    let some highByte := terms[31]? | throw "Bytes32 source term has no high byte"
    let low31 ← bytesFieldTerms terms 1
    pure (highByte, packByteTerms low31)
  | .select condition yes no => do
    let (yesHigh, yesLow) ← splitBytes32Fields yes
    let (noHigh, noLow) ← splitBytes32Fields no
    pure (.select condition yesHigh noHigh, .select condition yesLow noLow)
  | term =>
    if opaqueBytes32Value term then
      pure (encodedHashChunkTerm term 1, encodedHashChunkTerm term 0)
    else .error "Bytes32 normalization lost byte identity"

private def alignedBytes32Fields (value : Normalized) : Except String (Term × Term) := do
  splitBytes32Fields value.term

private def bytes32FromChunksTerm (low31 highByte : Term) : Term :=
  .unary "bytes32_from_chunks" (.hash [low31, highByte])

/-- A fixed byte projection after reconstructing canonical Bytes32 chunks. -/
def bytes32ByteAtTerm (bytes : Term) (index : Nat) : Term :=
  .unary s!"bytes32_byte_at:{index}" bytes

/-- Reversal preserves the typed byte sequence rather than reversing its field chunks. -/
def reverseBytes32Term (bytes : Term) : Term :=
  .unary "reverse_bytes32" bytes

def bytesChunkCount (length : Nat) : Nat := (length + 30) / 31

def bytesChunkWidth (length index : Nat) : Nat := min 31 (length - index * 31)

def encodedBytesChunkTerm (length : Nat) (bytes : Term) (index : Nat) : Term :=
  if length == 32 then encodedHashChunkTerm bytes index
  else .unary s!"encode_bytes:{length}:{index}" bytes

/-- Low-to-high canonical chunks, with legacy Bytes32 term identities retained. -/
def bytesChunksTerm (length : Nat) : Term → Except String (List Term)
  | .bytes terms => do
    unless terms.length == length do throw "byte source term has wrong length"
    pure ((List.range (bytesChunkCount length)).map fun index =>
      let chunk := (terms.drop (index * 31)).take 31
      if chunk.length == 1 then chunk.head! else packByteTerms chunk)
  | .select condition yes no => do
    let yes ← bytesChunksTerm length yes
    let no ← bytesChunksTerm length no
    pure ((yes.zip no).map fun (a, b) => .select condition a b)
  | term =>
    if opaqueBytes32Value term then
      pure ((List.range (bytesChunkCount length)).map (encodedBytesChunkTerm length term))
    else .error "byte normalization lost byte identity"

def bytesFromChunksTerm (length : Nat) (chunks : List Term) : Term :=
  if length == 32 then .unary "bytes32_from_chunks" (.hash chunks)
  else .unary s!"bytes_from_chunks:{length}" (.hash chunks)

def reverseBytesTerm (length : Nat) (bytes : Term) : Term :=
  if length == 32 then reverseBytes32Term bytes else .unary s!"reverse_bytes:{length}" bytes

def sliceBytesTerm (length start end_ : Nat) (bytes : Term) : Term :=
  .unary s!"slice_bytes:{length}:{start}:{end_}" bytes

def concatBytesTerm (leftLength rightLength : Nat) (left right : Term) : Term :=
  .binary s!"concat_bytes:{leftLength}:{rightLength}" left right

def bytesByteAtTerm (length : Nat) (bytes : Term) (index : Nat) : Term :=
  if length == 32 then bytes32ByteAtTerm bytes index
  else .unary s!"bytes_byte_at:{length}:{index}" bytes

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
        | .bytes _ | .jubjubScalar | .jubjubPoint => bounds} := rfl

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
  | .bytes32Literal values => pure {term := .bytes (values.map Term.constant)}
  | .bytesLiteral _ values => pure {term := .bytes (values.map Term.constant)}
  | .bytesField (length := length) value index => do
    let normalized ← normalize env value
    unless index < bytesChunkCount length do throw "byte field chunk index is out of range"
    let term ← match normalized.term with
      | .bytes terms => do
        unless terms.length == length do throw "byte source term has wrong length"
        pure (packByteTerms ((terms.drop ((bytesChunkCount length - 1 - index) * 31)).take 31))
      | other => do
        let chunks ← bytesChunksTerm length other
        let some chunk := chunks.reverse[index]? | throw "byte field chunk index is out of range"
        pure chunk
    pure {term, bounds := normalized.bounds, assertions := normalized.assertions}
  | .bytesAt (length := length) value index => do
    let normalized ← normalize env value
    unless index < length do throw "byte index is out of range"
    match normalized.term with
    | .bytes terms => do
      unless terms.length == length do throw "byte source term has wrong length"
      let some term := terms[index]? | throw "byte index is out of range"
      pure {term := term, bounds := normalized.bounds ++ [(term, 255)], assertions := normalized.assertions}
    | term => do
      let chunks ← bytesChunksTerm length term
      let reconstructed := bytesFromChunksTerm length chunks
      let byte := bytesByteAtTerm length reconstructed index
      pure {term := byte, bounds := normalized.bounds ++ [(byte, 255)], assertions := normalized.assertions}
  | .reverseBytes (length := length) value => do
    let normalized ← normalize env value
    let chunks ← bytesChunksTerm length normalized.term
    let term := if length == 0 then Term.bytes [] else
      reverseBytesTerm length (bytesFromChunksTerm length chunks)
    pure {normalized with term}
  | .sliceBytes (length := length) value start end_ => do
    let normalized ← normalize env value
    unless start ≤ end_ && end_ ≤ length do throw "byte slice is out of range"
    let chunks ← bytesChunksTerm length normalized.term
    let term := if start == end_ then Term.bytes [] else
      sliceBytesTerm length start end_ (bytesFromChunksTerm length chunks)
    pure {normalized with term}
  | .concatBytes (leftLength := leftLength) (rightLength := rightLength) left right => do
    let left ← normalize env left
    let right ← normalize env right
    let leftChunks ← bytesChunksTerm leftLength left.term
    let rightChunks ← bytesChunksTerm rightLength right.term
    let term := if leftLength == 0 then right.term else if rightLength == 0 then left.term else
      concatBytesTerm leftLength rightLength
        (bytesFromChunksTerm leftLength leftChunks) (bytesFromChunksTerm rightLength rightChunks)
    pure {term, bounds := left.bounds ++ right.bounds, assertions := left.assertions ++ right.assertions}
  | .sha512 (length := length) value => do
    let normalized ← normalize env value
    let chunks ← bytesChunksTerm length normalized.term
    pure {normalized with term := fixedByteHashTerm "sha512" length chunks.reverse}
  | .keccak256 (length := length) value => do
    let normalized ← normalize env value
    let chunks ← bytesChunksTerm length normalized.term
    pure {normalized with term := fixedByteHashTerm "keccak256" length chunks.reverse}
  | .persistentHash32 value => do
    let normalized ← normalize env value
    let (highByte, low31) ← alignedBytes32Fields normalized
    let term := persistentHash32Term highByte low31
    pure {term, bounds := normalized.bounds, assertions := normalized.assertions}
  | .persistentHashVector32 values => do
    let normalized ← values.mapM (normalize env)
    let fields ← normalized.mapM alignedBytes32Fields
    let term := persistentHashVector32Term fields
    let bounds := (normalized.map (fun item => item.bounds)).flatten
    let assertions := (normalized.map (fun item => item.assertions)).flatten
    pure {term, bounds, assertions}
  | .persistentHashNative value => do
    let normalized ← normalize env value
    let term := persistentHashNativeTerm normalized.term
    pure {term := term, bounds := normalized.bounds, assertions := normalized.assertions}
  | .persistentHashNativeVector values => do
    unless values.length ≥ 1 && values.length ≤ 32 do
      throw "Native persistent-hash vector must contain 1 to 32 fields"
    let normalized ← values.mapM (normalize env)
    let term := persistentHashNativeVectorTerm (normalized.map (·.term))
    let bounds := (normalized.map (fun item => item.bounds)).flatten
    let assertions := (normalized.map (fun item => item.assertions)).flatten
    pure {term, bounds, assertions}
  | .reverseBytes32 value => do
    let normalized ← normalize env value
    let (highByte, low31) ← alignedBytes32Fields normalized
    let bytes := bytes32FromChunksTerm low31 highByte
    pure {normalized with term := reverseBytes32Term bytes}
  | .toBytes32 (source := source) value => do
    let normalized ← normalize env value
    let opcode := match source with
      | .native => "to_bytes32_native"
      | .jubjubScalar => "to_bytes32_jubjub_scalar"
      | .jubjubPoint => "to_bytes32_jubjub_point"
      | _ => "to_bytes32_unsupported"
    pure (Normalized.mk (.unary opcode normalized.term) normalized.bounds normalized.assertions)
  | .fromBytes32 (target := target) value => do
    let normalized ← normalize env value
    let (highByte, low31) ← alignedBytes32Fields normalized
    let rawBytes := bytes32FromChunksTerm low31 highByte
    let (opcode, maximum?, assertions) ← match target with
      | .native => pure ("from_bytes32_native", some (Field.modulus - 1),
          normalized.assertions)
      | .jubjubScalar => pure ("from_bytes32_jubjub_scalar", some (Jubjub.scalarOrder - 1),
          normalized.assertions)
      | .jubjubPoint => do
        let point := Term.unary "from_bytes32_jubjub_point" rawBytes
        let encoded := Term.unary "to_bytes32_jubjub_point" point
        let (encodedHigh, encodedLow) ← splitBytes32Fields encoded
        pure ("from_bytes32_jubjub_point", none,
          normalized.assertions ++ [
            .binary "test_eq" highByte encodedHigh,
            .binary "test_eq" low31 encodedLow])
      | _ => throw "fromBytes32 supports only Native, JubjubScalar and JubjubPoint"
    let term := .unary opcode rawBytes
    let bounds := normalized.bounds ++ (maximum?.toList.map fun maximum => (term, maximum))
    pure {term, bounds, assertions}
  | .jubjubScalarFromNative value => do
    let normalized ← normalize env value
    let term : Term := .unary "jubjub_scalar_from_native" normalized.term
    pure {term, bounds := normalized.bounds, assertions := normalized.assertions}
  | .jubjubScalarToNative value => do
    let normalized ← normalize env value
    let term : Term := .unary "jubjub_scalar_to_native" normalized.term
    pure {term, bounds := normalized.bounds, assertions := normalized.assertions}
  | .jubjubMulGenerator scalar => do
    let normalized ← normalize env scalar
    let term : Term := .unary "ec_mul_generator_jubjub" normalized.term
    pure {term, bounds := normalized.bounds, assertions := normalized.assertions}
  | .jubjubMul point scalar => do
    let point ← normalize env point
    let scalar ← normalize env scalar
    let term : Term := .binary "ec_mul_jubjub" point.term scalar.term
    pure (Normalized.mk term (point.bounds ++ scalar.bounds)
      (point.assertions ++ scalar.assertions))
  | .jubjubAdd left right => do
    let left ← normalize env left
    let right ← normalize env right
    let term : Term := .binary "add_jubjub_point" left.term right.term
    pure (Normalized.mk term (left.bounds ++ right.bounds)
      (left.assertions ++ right.assertions))
  | .jubjubNeg point => do
    let point ← normalize env point
    let term : Term := .unary "neg_jubjub_point" point.term
    pure {term, bounds := point.bounds, assertions := point.assertions}
  | .jubjubCoordinate point index => do
    let point ← normalize env point
    let term : Term := .unary (if index == 0 then "jubjub_x" else "jubjub_y") point.term
    pure {term, bounds := point.bounds, assertions := point.assertions}
  | .jubjubFromCoordinates x y => do
    let x ← normalize env x
    let y ← normalize env y
    let term : Term := .binary "from_coordinates_jubjub" x.term y.term
    pure (Normalized.mk term (x.bounds ++ y.bounds) (x.assertions ++ y.assertions))
  | .ref name => do
    let some term := env.lookup name | throw s!"unbound native source symbol '{name}'"
    pure (requireSourceType ty term [])
  | .add left right => do pure (arithmetic ty "add" (← normalize env left) (← normalize env right))
  | .mul left right => do pure (arithmetic ty "mul" (← normalize env left) (← normalize env right))
  | .sub left right => do pure (subtraction ty (← normalize env left) (← normalize env right))
  | .uadd left right => do pure (arithmetic ty "add" (← normalize env left) (← normalize env right))
  | .umul left right => do pure (arithmetic ty "mul" (← normalize env left) (← normalize env right))
  | .usub left right => do pure (subtraction ty (← normalize env left) (← normalize env right))
  | .inv value => do
    let normalized ← normalize env value
    let (opcode, maximum, nonzeroInput) ← match ty with
      | .native => pure ("inverse_native", Field.modulus - 1, normalized.term)
      | .jubjubScalar => pure ("inverse_jubjub_scalar", Jubjub.scalarOrder - 1,
          .unary "jubjub_scalar_to_native" normalized.term)
      | _ => throw "inverse supports only Native and JubjubScalar"
    let nonzero := .unary "not" (.binary "test_eq" nonzeroInput (.constant 0))
    pure {
      term := .unary opcode normalized.term
      bounds := normalized.bounds ++ [(normalized.term, maximum)]
      assertions := normalized.assertions ++ [nonzero] }
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
  /-- This raw Native input also represents a typed JubjubScalar parameter and
  must pass the source scalar's canonical reduce/encode equality bridge. -/
  canonicalJubjubScalar : Bool := false
  /-- Conditional transcript consumption is allowed only for source-bound public reads. -/
  activityGuard : Option Term := none
  deriving Repr

def InputRequirement.byte (input : Input) (index : Nat) : InputRequirement :=
  {identifier := input.nativeIdentifiers[index]!, visibility := input.visibility, ty := .uint 255}

private def jubjubScalarInputRequirement (input : Input) : InputRequirement :=
  {identifier := "%input_" ++ input.name, visibility := input.visibility,
    ty := .native, canonicalJubjubScalar := true}

def Input.requirements (input : Input) : List InputRequirement :=
  match input.ty with
  | .bytes length => (List.range length).map (InputRequirement.byte input)
  | .jubjubScalar => [jubjubScalarInputRequirement input]
  | .jubjubPoint => input.nativeIdentifiers.map fun identifier =>
      {identifier, visibility := input.visibility, ty := .native}
  | _ => [{identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}]

def Input.sourceTerm (input : Input) : Term :=
  match input.ty with
  | .bytes _ => .bytes (input.nativeIdentifiers.map Term.input)
  | .jubjubScalar => .unary "jubjub_scalar_from_native" (.input ("%input_" ++ input.name))
  | .jubjubPoint => .binary "from_coordinates_jubjub"
      (.input input.nativeIdentifiers[0]!) (.input input.nativeIdentifiers[1]!)
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

end Noctium.Backend.Native
