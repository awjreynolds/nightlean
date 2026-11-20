import Init.Data.Nat.PowMod
import Noctium.Disclosure

namespace Noctium

abbrev Ty.Denote : Ty → Type
  | .native => Nat
  | .bool => Bool
  | .uint _ => Nat
  | .bytes _ => List Nat
  | .jubjubScalar => Nat
  | .jubjubPoint => Nat × Nat
  | .foreign kind => kind.Denote

inductive Value where
  | native (value : Nat)
  | bool (value : Bool)
  | uint (maximum value : Nat)
  | bytes (length : Nat) (value : List Nat)
  | jubjubScalar (value : Nat)
  | jubjubPoint (x y : Nat)
  | foreignBase (curve : Foreign.Curve) (value : Nat)
  | foreignScalar (curve : Foreign.Curve) (value : Nat)
  | foreignPoint (curve : Foreign.Curve) (value : Foreign.Point)
  deriving Repr, BEq, DecidableEq

def Value.as : (ty : Ty) → Value → Option ty.Denote
  | .native, .native n => some n
  | .bool, .bool b => some b
  | .uint maximum, .uint found n => if maximum == found then some n else none
  | .bytes length, .bytes found values =>
    if length == found && values.length == length && values.all (· ≤ 255) then some values else none
  | .jubjubScalar, .jubjubScalar scalar => some scalar
  | .jubjubPoint, .jubjubPoint x y => some (x, y)
  | .foreign (.base curve), .foreignBase found value =>
    if curve == found && value < curve.baseModulus then some value else none
  | .foreign (.scalar curve), .foreignScalar found value =>
    if curve == found && value < curve.scalarModulus then some value else none
  | .foreign (.point curve), .foreignPoint found value =>
    if curve == found && Foreign.pointValid curve value then some value else none
  | _, _ => none

def Value.pack : (ty : Ty) → ty.Denote → Value
  | .native, n => .native n
  | .bool, b => .bool b
  | .uint maximum, n => .uint maximum n
  | .bytes length, values => .bytes length values
  | .jubjubScalar, scalar => .jubjubScalar scalar
  | .jubjubPoint, (x, y) => .jubjubPoint x y
  | .foreign (.base curve), value => .foreignBase curve value
  | .foreign (.scalar curve), value => .foreignScalar curve value
  | .foreign (.point curve), value => .foreignPoint curve value

/-- Recursive semantic form used by the nested-map source effects. -/
inductive LedgerValue where
  | scalar (value : Value)
  | map (entries : List (Value × LedgerValue))
  | composite (type : Types.CompositeType) (leaves : List Nat)
  | list (entries : List (List Nat))
  deriving Repr, BEq

abbrev EvalEnv := List (String × Value)

structure JubjubOracle where
  pointValid : Nat × Nat → Except String Unit :=
    fun _ => .error "qualified Jubjub point-validation oracle is unavailable"
  fromCoordinates : Nat → Nat → Except String (Nat × Nat) :=
    fun _ _ => .error "qualified Jubjub coordinate oracle is unavailable"
  mulGenerator : Nat → Except String (Nat × Nat) :=
    fun _ => .error "qualified Jubjub generator-multiplication oracle is unavailable"
  mul : (Nat × Nat) → Nat → Except String (Nat × Nat) :=
    fun _ _ => .error "qualified Jubjub multiplication oracle is unavailable"
  add : (Nat × Nat) → (Nat × Nat) → Except String (Nat × Nat) :=
    fun _ _ => .error "qualified Jubjub addition oracle is unavailable"
  neg : (Nat × Nat) → Except String (Nat × Nat) :=
    fun _ => .error "qualified Jubjub negation oracle is unavailable"
  /-- Qualified native hash-to-curve oracle. -/
  hashToCurve : List Nat → Except String (Nat × Nat) :=
    fun _ => .error "qualified hash_to_curve oracle is unavailable"

/-- Point operations and compressed SEC1 byte conversion fail closed until a
qualified implementation supplies the pinned curve backend. Field arithmetic
and field byte conversion use the checked Nat definitions below. -/
structure ForeignOracle where
  pointAdd : Foreign.Curve → Foreign.Point → Foreign.Point → Except String Foreign.Point :=
    fun _ _ _ => .error "qualified foreign point-addition oracle is unavailable"
  pointMul : Foreign.Curve → Foreign.Point → Nat → Except String Foreign.Point :=
    fun _ _ _ => .error "qualified foreign point-multiplication oracle is unavailable"
  mulGenerator : Foreign.Curve → Nat → Except String Foreign.Point :=
    fun _ _ => .error "qualified foreign generator-multiplication oracle is unavailable"
  pointToBytes : Foreign.Curve → Foreign.Point → Except String (List Nat) :=
    fun _ _ => .error "qualified foreign point-serialization oracle is unavailable"
  pointFromBytes : Foreign.Curve → List Nat → Except String Foreign.Point :=
    fun _ _ => .error "qualified foreign point-decoding oracle is unavailable"

/-- Crypto oracles have fail-closed defaults. A backend must supply pinned hash
and Jubjub operations before semantic evaluation can execute those expressions. -/
structure EvalContext where
  modulus : Nat
  poseidon2 : Nat → Nat → Nat → Except String Nat
  /-- Qualified pinned native transient_hash oracle. -/
  transientHash : List Nat → Except String Nat :=
    fun _ => .error "qualified transient_hash oracle is unavailable"
  /-- Qualified host implementation of the pinned Bytes32 persistent hash.
  The default rejects, so evaluation never substitutes a placeholder hash. -/
  persistentHash32 : List Nat → Except String (List Nat) :=
    fun _ => .error "qualified Bytes32 persistent-hash oracle is unavailable"
  /-- Qualified SHA-512 oracle for source byte strings. -/
  sha512 : List Nat → Except String (List Nat) :=
    fun _ => .error "qualified SHA-512 oracle is unavailable"
  /-- Qualified Keccak-256 oracle for source byte strings. -/
  keccak256 : List Nat → Except String (List Nat) :=
    fun _ => .error "qualified Keccak-256 oracle is unavailable"
  jubjub : JubjubOracle := {}
  foreign : ForeignOracle := {}
  /-- Pinned native serialization of validated Jubjub affine points. -/
  jubjubToBytes32 : (Nat × Nat) → Except String (List Nat) :=
    fun _ => .error "qualified Jubjub byte-serialization oracle is unavailable"
  /-- Pinned strict compressed Jubjub decoder, including subgroup checks. -/
  jubjubFromBytes32 : List Nat → Except String (Nat × Nat) :=
    fun _ => .error "qualified Jubjub byte-decoding oracle is unavailable"
  /-- Address of an immediate contract caller, supplied by the execution context. -/
  contractCaller : Option (List Nat) := none

private def sameValue : (ty : Ty) → ty.Denote → ty.Denote → Bool
  | .native, a, b => a == b
  | .bool, a, b => a == b
  | .uint _, a, b => a == b
  | .bytes _, a, b => a == b
  | .jubjubScalar, a, b => a == b
  | .jubjubPoint, a, b => a == b
  | .foreign _, a, b => a == b

private def canonical (ctx : EvalContext) (ty : Ty) (v : ty.Denote) : Bool :=
  match ty with
  | .native => v < ctx.modulus
  | .bool => true
  | .uint maximum => maximum ≤ ScalarPolicy.maxUint && v ≤ maximum && v < ctx.modulus
  | .bytes length => v.length == length && v.all (· ≤ 255)
  | .jubjubScalar => v < Jubjub.scalarOrder
  | .jubjubPoint => v.1 < ctx.modulus && v.2 < ctx.modulus &&
      (ctx.jubjub.pointValid v).isOk
  | .foreign kind => kind.canonical v

/-- Public reduction equation for input-admission and preservation proofs. -/
theorem canonical_eq (ctx : EvalContext) (ty : Ty) (value : ty.Denote) :
    canonical ctx ty value = match ty with
      | .native => value < ctx.modulus
      | .bool => true
      | .uint maximum => maximum ≤ ScalarPolicy.maxUint && value ≤ maximum && value < ctx.modulus
      | .bytes length => value.length == length && value.all (· ≤ 255)
      | .jubjubScalar => value < Jubjub.scalarOrder
      | .jubjubPoint => value.1 < ctx.modulus && value.2 < ctx.modulus &&
          (ctx.jubjub.pointValid value).isOk
      | .foreign kind => kind.canonical value := rfl

private def scalarNumber : (ty : Ty) → ty.Denote → Except String Nat
  | .native, n | .uint _, n => pure n
  | .bool, b => pure (if b then 1 else 0)
  | .bytes _, _ => .error "byte strings do not support scalar conversion"
  | .jubjubScalar, _ => .error "Jubjub scalars do not support scalar conversion"
  | .jubjubPoint, _ => .error "Jubjub points do not support scalar conversion"
  | .foreign _, _ => .error "foreign values do not support scalar conversion"

private def scalarCast (ctx : EvalContext) (target : Ty) (number : Nat) : Except String target.Denote :=
  match target with
  | .native => if number < ctx.modulus then pure number else .error "noncanonical scalar conversion"
  | .bool => pure (number != 0)
  | .uint maximum =>
    if maximum ≤ ScalarPolicy.maxUint && number ≤ maximum && number < ctx.modulus then pure number
    else .error "scalar conversion exceeds unsigned bound"
  | .bytes _ => .error "byte strings do not support scalar conversion"
  | .jubjubScalar | .jubjubPoint => .error "Jubjub values do not support scalar conversion"
  | .foreign _ => .error "foreign values do not support scalar conversion"

private def checkedJubjubPoint (ctx : EvalContext) (point : Nat × Nat) :
    Except String (Nat × Nat) := do
  if point.1 >= ctx.modulus || point.2 >= ctx.modulus then
    throw "noncanonical Jubjub coordinate"
  ctx.jubjub.pointValid point
  pure point

/-- Pinned native Bytes field packing: little-endian bytes within each
FR_BYTES_STORED-sized chunk, with the chunk sequence reversed. For Bytes32 the
two chunks are byte 31 first, followed by bytes 0 through 30. -/
private def bytesFieldChunk (length chunkIndex : Nat) (values : List Nat) : Nat := Id.run do
  let chunks := (length + 30) / 31
  let rawIndex := chunks - 1 - chunkIndex
  let start := rawIndex * 31
  let size := min 31 (length - start)
  let part := values.drop start |>.take size
  let mut result := 0
  for (value, index) in part.zipIdx do
    result := result + value * 256 ^ index
  return result

private def nativeFieldBytesLE (value : Nat) : List Nat :=
  go value 32
where
  go (remaining : Nat) : Nat → List Nat
    | 0 => []
    | count + 1 => remaining % 256 :: go (remaining / 256) count

private def evaluatePersistentHash (ctx : EvalContext) (preimage : List Nat) :
    Except String (List Nat) := do
  let result ← ctx.persistentHash32 preimage
  if result.length != 32 || !result.all (· ≤ 255) then
    throw "persistent-hash oracle returned a malformed Bytes32 digest"
  pure result

private def bytes32IntegerLE (values : List Nat) : Nat := Id.run do
  let mut result := 0
  for (value, index) in values.zipIdx do result := result + value * 256 ^ index
  return result

private def checkedPrimeFieldInverse (value modulus : Nat) : Except String Nat := do
  if modulus ≤ 2 then throw "invalid prime-field modulus for inverse"
  if value == 0 then throw "inverse of zero is undefined"
  if value ≥ modulus then throw "inverse operand is outside its prime field"
  let inverse := Nat.powMod value (modulus - 2) modulus
  if value * inverse % modulus != 1 then
    throw "prime-field inverse failed its multiplication postcondition"
  pure inverse

private def integerBytesLE (value length : Nat) : List Nat :=
  (List.range length).map fun index => (value / 256 ^ index) % 256

private def checkedForeignPoint (curve : Foreign.Curve) (point : Foreign.Point) :
    Except String Foreign.Point := do
  unless Foreign.pointValid curve point do throw "foreign point is not canonical or on curve"
  pure point

private def checkedForeignBytes (length : Nat) (bytes : List Nat) :
    Except String (List Nat) := do
  unless bytes.length == length && bytes.all (· ≤ 255) do
    throw "foreign byte oracle returned a malformed encoding"
  pure bytes

private def checkForeignByteInput (length : Nat) (bytes : List Nat) : Except String Unit := do
  if length > maxBytesLength then
    throw s!"byte string length exceeds the maximum of {maxBytesLength}"
  unless bytes.length == length && bytes.all (· ≤ 255) do
    throw "foreign byte input is not a canonical fixed byte string"
private def checkedForeignToBytes : (ctx : EvalContext) → (kind : Foreign.Kind) →
    kind.Denote → Except String (List Nat)
  | _, .base curve, value => do
    unless value < curve.baseModulus do throw "foreign base value is noncanonical"
    pure (integerBytesLE value 32)
  | _, .scalar curve, value => do
    unless value < curve.scalarModulus do throw "foreign scalar value is noncanonical"
    pure (integerBytesLE value 32)
  | ctx, .point curve, point => do
    let point ← checkedForeignPoint curve point
    let bytes ← ctx.foreign.pointToBytes curve point
    checkedForeignBytes (Foreign.Kind.point curve).byteLength bytes

private def checkedForeignFromBytes : (ctx : EvalContext) → (kind : Foreign.Kind) →
    (length : Nat) → (bytes : List Nat) → Except String kind.Denote
  | _, .base curve, length, bytes => do
    checkForeignByteInput length bytes
    pure (bytes32IntegerLE bytes % curve.baseModulus)
  | _, .scalar curve, length, bytes => do
    checkForeignByteInput length bytes
    pure (bytes32IntegerLE bytes % curve.scalarModulus)
  | ctx, .point curve, length, bytes => do
    checkForeignByteInput length bytes
    unless length == (Foreign.Kind.point curve).byteLength do
      throw s!"foreign point decoding requires exactly {(Foreign.Kind.point curve).byteLength} bytes"
    let point ← ctx.foreign.pointFromBytes curve bytes
    let point := match point with
      | .affine x y => Foreign.normalizePoint curve x y
      | .identity => .identity
    let point ← checkedForeignPoint curve point
    let encoded ← ctx.foreign.pointToBytes curve point
    let encoded ← checkedForeignBytes (Foreign.Kind.point curve).byteLength encoded
    unless encoded == bytes do throw "foreign point byte encoding is not canonical"
    pure point

private def checkedForeignUnary : (ctx : EvalContext) → (operation : Foreign.UnaryOp) →
    operation.inputKind.Denote → Except String operation.outputKind.Denote
  | _, .neg (.base curve), value => do
    unless value < curve.baseModulus do throw "foreign base negation input is noncanonical"
    pure ((curve.baseModulus - value) % curve.baseModulus)
  | _, .neg (.scalar curve), value => do
    unless value < curve.scalarModulus do throw "foreign scalar negation input is noncanonical"
    pure ((curve.scalarModulus - value) % curve.scalarModulus)
  | _, .neg (.point curve), point => do
    let point ← checkedForeignPoint curve point
    match point with
    | .identity => pure .identity
    | .affine x y =>
      if curve == .curve25519 then
        checkedForeignPoint curve (Foreign.normalizePoint curve ((curve.baseModulus - x) % curve.baseModulus) y)
      else
        checkedForeignPoint curve (.affine x ((curve.baseModulus - y) % curve.baseModulus))
  | _, .inv (.base curve), value => do
    unless value < curve.baseModulus do throw "foreign inverse input is noncanonical"
    checkedPrimeFieldInverse value curve.baseModulus
  | _, .inv (.scalar curve), value => do
    unless value < curve.scalarModulus do throw "foreign inverse input is noncanonical"
    checkedPrimeFieldInverse value curve.scalarModulus
  | ctx, .mulGenerator curve, scalar => do
    unless scalar < curve.scalarModulus do throw "foreign generator scalar is noncanonical"
    checkedForeignPoint curve (← ctx.foreign.mulGenerator curve scalar)
  | _, .x curve, point => do
    let point ← checkedForeignPoint curve point
    match point with
    | .identity => if curve == .curve25519 then pure 0 else throw "foreign identity has no affine x coordinate"
    | .affine x _ => pure x
  | _, .y curve, point => do
    let point ← checkedForeignPoint curve point
    match point with
    | .identity => if curve == .curve25519 then pure 1 else throw "foreign identity has no affine y coordinate"
    | .affine _ y => pure y

private def checkedForeignBinary : (ctx : EvalContext) → (operation : Foreign.BinaryOp) →
    operation.leftKind.Denote → operation.rightKind.Denote →
    Except String operation.outputKind.Denote
  | _, .add (.base curve), left, right => do
    unless left < curve.baseModulus && right < curve.baseModulus do throw "foreign base addition input is noncanonical"
    pure ((left + right) % curve.baseModulus)
  | _, .add (.scalar curve), left, right => do
    unless left < curve.scalarModulus && right < curve.scalarModulus do throw "foreign scalar addition input is noncanonical"
    pure ((left + right) % curve.scalarModulus)
  | ctx, .add (.point curve), left, right => do
    let left ← checkedForeignPoint curve left
    let right ← checkedForeignPoint curve right
    checkedForeignPoint curve (← ctx.foreign.pointAdd curve left right)
  | _, .sub (.base curve), left, right => do
    unless left < curve.baseModulus && right < curve.baseModulus do throw "foreign base subtraction input is noncanonical"
    pure ((curve.baseModulus + left - right) % curve.baseModulus)
  | _, .sub (.scalar curve), left, right => do
    unless left < curve.scalarModulus && right < curve.scalarModulus do throw "foreign scalar subtraction input is noncanonical"
    pure ((curve.scalarModulus + left - right) % curve.scalarModulus)
  | ctx, .sub (.point curve), left, right => do
    let left ← checkedForeignPoint curve left
    let right ← checkedForeignPoint curve right
    let negative ← match right with
      | .identity => pure .identity
      | .affine x y =>
        if curve == .curve25519 then
          checkedForeignPoint curve (Foreign.normalizePoint curve ((curve.baseModulus - x) % curve.baseModulus) y)
        else
          checkedForeignPoint curve (.affine x ((curve.baseModulus - y) % curve.baseModulus))
    checkedForeignPoint curve (← ctx.foreign.pointAdd curve left negative)
  | _, .mul (.base curve), left, right => do
    unless left < curve.baseModulus && right < curve.baseModulus do throw "foreign base multiplication input is noncanonical"
    pure ((left * right) % curve.baseModulus)
  | _, .mul (.scalar curve), left, right => do
    unless left < curve.scalarModulus && right < curve.scalarModulus do throw "foreign scalar multiplication input is noncanonical"
    pure ((left * right) % curve.scalarModulus)
  | ctx, .ecMul curve, point, scalar => do
    let point ← checkedForeignPoint curve point
    unless scalar < curve.scalarModulus do throw "foreign point-multiplication scalar is noncanonical"
    checkedForeignPoint curve (← ctx.foreign.pointMul curve point scalar)
  | _, .fromCoordinates curve, x, y => do
    unless x < curve.baseModulus && y < curve.baseModulus do throw "foreign coordinates are noncanonical"
    checkedForeignPoint curve (Foreign.normalizePoint curve x y)

/-- Evaluation is total and returns errors for absent/mistyped witnesses or
noncanonical field data, rather than silently inventing witness values. -/
def Expr.eval (ctx : EvalContext) (env : EvalEnv) : Expr ty → Except String ty.Denote
  | .native n => if n < ctx.modulus then pure n else .error "noncanonical native constant"
  | .bool b => .ok b
  | .boolAnd left right => do
    let left ← left.eval ctx env
    let right ← right.eval ctx env
    pure (left && right)
  | .boolOr left right => do
    let left ← left.eval ctx env
    let right ← right.eval ctx env
    pure (left || right)
  | .boolXor left right => do
    let left ← left.eval ctx env
    let right ← right.eval ctx env
    pure (left != right)
  | .uint maximum n =>
    if canonical ctx (.uint maximum) n then pure n else .error "noncanonical unsigned constant"
  | .bytesField (length := length) value index => do
    let values ← value.eval ctx env
    let result := bytesFieldChunk length index values
    if result < ctx.modulus then pure result else .error "noncanonical packed byte field"
  | .bytes32Literal values =>
    if values.length == 32 && values.all (· ≤ 255) then pure values
    else .error "Bytes32 literal must contain exactly 32 byte values"
  | .bytesLiteral length values =>
    if length ≤ maxBytesLength && values.length == length && values.all (· ≤ 255) then
      pure values
    else .error "byte literal must contain exactly its declared number of byte values"
  | .reverseBytes value => do
    pure ((← value.eval ctx env).reverse)
  | .sliceBytes value start stop => do
    let bytes ← value.eval ctx env
    if start > stop || stop > bytes.length then throw "byte slice bounds are out of range"
    pure ((bytes.drop start).take (stop - start))
  | .concatBytes left right => do
    pure ((← left.eval ctx env) ++ (← right.eval ctx env))
  | .sha512 (length := length) value => do
    if length > maxBytesLength then
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
    let input ← value.eval ctx env
    if input.length != length || !input.all (· ≤ 255) then
      throw "SHA-512 input is not a canonical fixed byte string"
    let digest ← ctx.sha512 input
    if digest.length != 64 || !digest.all (· ≤ 255) then
      throw "SHA-512 oracle returned a malformed Bytes64 digest"
    pure digest
  | .keccak256 (length := length) value => do
    if length > maxBytesLength then
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
    let input ← value.eval ctx env
    if input.length != length || !input.all (· ≤ 255) then
      throw "Keccak-256 input is not a canonical fixed byte string"
    let digest ← ctx.keccak256 input
    if digest.length != 32 || !digest.all (· ≤ 255) then
      throw "Keccak-256 oracle returned a malformed Bytes32 digest"
    pure digest
  | .reverseBytes32 value => do
    pure ((← value.eval ctx env).reverse)
  | .jubjubScalarFromNative value => do
    pure ((← value.eval ctx env) % Jubjub.scalarOrder)
  | .jubjubScalarToNative value => do
    let scalar ← value.eval ctx env
    if scalar < ctx.modulus then pure scalar else .error "Jubjub scalar does not fit Native"
  | .jubjubMulGenerator scalar => do
    checkedJubjubPoint ctx (← ctx.jubjub.mulGenerator (← scalar.eval ctx env))
  | .jubjubMul point scalar => do
    checkedJubjubPoint ctx (← ctx.jubjub.mul (← point.eval ctx env) (← scalar.eval ctx env))
  | .jubjubAdd left right => do
    checkedJubjubPoint ctx (← ctx.jubjub.add (← left.eval ctx env) (← right.eval ctx env))
  | .jubjubNeg point => do
    checkedJubjubPoint ctx (← ctx.jubjub.neg (← point.eval ctx env))
  | .jubjubCoordinate point index => do
    let (x, y) ← point.eval ctx env
    match index with
    | 0 => pure x
    | 1 => pure y
    | _ => throw "Jubjub coordinate index must be 0 or 1"
  | .jubjubFromCoordinates x y => do
    checkedJubjubPoint ctx (← ctx.jubjub.fromCoordinates (← x.eval ctx env) (← y.eval ctx env))
  | .hashToCurve values => do
    if values.length > Types.defaultLimits.maxVectorLength then
      throw s!"hash_to_curve input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    let mut reversedInputs := []
    for value in values do
      let field ← value.eval ctx env
      if field >= ctx.modulus then throw "noncanonical hash_to_curve Native input"
      reversedInputs := field :: reversedInputs
    let inputs := reversedInputs.reverse
    checkedJubjubPoint ctx (← ctx.jubjub.hashToCurve inputs)
  | .foreignBase curve value =>
    if value < curve.baseModulus then pure value else .error "foreign base-field constant is not canonical"
  | .foreignScalar curve value =>
    if value < curve.scalarModulus then pure value else .error "foreign scalar constant is not canonical"
  | .foreignIdentity _ => pure .identity
  | .foreignEncodedField (kind := kind) value index => do
    let encoded ← Foreign.encodeValue kind (← value.eval ctx env)
    match encoded[index]? with
    | some field =>
      if field < ctx.modulus then pure field else throw "foreign Encode field is noncanonical"
    | none => throw "foreign encoded-field index is out of range"
  | .foreignUnary operation value => do
    checkedForeignUnary ctx operation (← value.eval ctx env)
  | .foreignBinary operation left right => do
    let left ← left.eval ctx env
    let right ← right.eval ctx env
    checkedForeignBinary ctx operation left right
  | .foreignToBytes (kind := kind) value => do
    checkedForeignToBytes ctx kind (← value.eval ctx env)
  | .foreignFromBytes (kind := kind) (length := length) value => do
    let bytes ← value.eval ctx env
    checkedForeignFromBytes ctx kind length bytes
  | .bytesAt (length := length) value index => do
    let values ← value.eval ctx env
    match values[index]? with
    | some byte =>
      if byte ≤ 255 then pure byte
      else if length == 32 then .error "noncanonical Bytes32 byte"
      else .error "noncanonical byte value"
    | none =>
      if length == 32 then .error "Bytes32 byte index is out of range"
      else .error "byte index is out of range"
  | .persistentHash32 value => do
    let input ← value.eval ctx env
    evaluatePersistentHash ctx input
  | .persistentHashVector32 values => do
    if values.length < 1 || values.length > 32 then
      throw "persistent hash vector must contain 1 to 32 Bytes32 values"
    let mut preimage := []
    for value in values do preimage := preimage ++ (← value.eval ctx env)
    evaluatePersistentHash ctx preimage
  | .persistentHashNative value => do
    let field ← value.eval ctx env
    evaluatePersistentHash ctx (nativeFieldBytesLE field)
  | .persistentHashNativeVector values => do
    if values.isEmpty || values.length > 32 then
      throw "Native persistent-hash vector must contain 1 to 32 fields"
    let mut preimage := []
    for value in values do
      preimage := preimage ++ nativeFieldBytesLE (← value.eval ctx env)
    evaluatePersistentHash ctx preimage
  | .toBytes32 (source := .native) value => do
    pure (nativeFieldBytesLE (← value.eval ctx env))
  | .toBytes32 (source := .jubjubScalar) value => do
    pure (nativeFieldBytesLE (← value.eval ctx env))
  | .toBytes32 (source := .jubjubPoint) value => do
    let point ← value.eval ctx env
    let _ ← checkedJubjubPoint ctx point
    let bytes ← ctx.jubjubToBytes32 point
    if bytes.length != 32 || !bytes.all (· ≤ 255) then
      throw "Jubjub byte-serialization oracle returned malformed Bytes32"
    pure bytes
  | .toBytes32 _ => .error "toBytes32 supports only Native, JubjubScalar and JubjubPoint"
  | .fromBytes32 (target := .native) value => do
    let bytes ← value.eval ctx env
    if ctx.modulus == 0 then throw "invalid zero Native modulus for Bytes32 decoding"
    pure (bytes32IntegerLE bytes % ctx.modulus)
  | .fromBytes32 (target := .jubjubScalar) value => do
    let bytes ← value.eval ctx env
    pure (bytes32IntegerLE bytes % Jubjub.scalarOrder)
  | .fromBytes32 (target := .jubjubPoint) value => do
    let bytes ← value.eval ctx env
    let point ← ctx.jubjubFromBytes32 bytes
    let _ ← checkedJubjubPoint ctx point
    let encoded ← ctx.jubjubToBytes32 point
    if encoded != bytes then throw "noncanonical Jubjub Bytes32 point encoding"
    pure point
  | .fromBytes32 _ => .error "fromBytes32 supports only Native, JubjubScalar and JubjubPoint"
  | .fromBytes (target := .native) (length := length) value => do
    let bytes ← value.eval ctx env
    if length > maxBytesLength then
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
    if ctx.modulus == 0 then throw "invalid zero Native modulus for byte decoding"
    pure (bytes32IntegerLE bytes % ctx.modulus)
  | .fromBytes (target := .jubjubScalar) (length := length) value => do
    let bytes ← value.eval ctx env
    if length > maxBytesLength then
      throw s!"byte string length exceeds the maximum of {maxBytesLength}"
    pure (bytes32IntegerLE bytes % Jubjub.scalarOrder)
  | .fromBytes _ => .error "fromBytes supports only Native and JubjubScalar"
  | .inv (ty := .native) value => do
    checkedPrimeFieldInverse (← value.eval ctx env) ctx.modulus
  | .inv (ty := .jubjubScalar) value => do
    checkedPrimeFieldInverse (← value.eval ctx env) Jubjub.scalarOrder
  | .inv _ => .error "inverse supports only Native and JubjubScalar"
  | .ref name => do
    let some raw := env.lookup name | throw s!"missing value '{name}'"
    let some value := raw.as ty | throw s!"value type mismatch for '{name}'"
    if !canonical ctx ty value then throw s!"noncanonical value '{name}'"
    pure value
  | .add a b => do
    if ctx.modulus == 0 then throw "invalid zero field modulus"
    pure (((← a.eval ctx env) + (← b.eval ctx env)) % ctx.modulus)
  | .mul a b => do
    if ctx.modulus == 0 then throw "invalid zero field modulus"
    pure (((← a.eval ctx env) * (← b.eval ctx env)) % ctx.modulus)
  | .sub a b => do
    if ctx.modulus == 0 then throw "invalid zero field modulus"
    pure ((ctx.modulus + (← a.eval ctx env) - (← b.eval ctx env)) % ctx.modulus)
  | .uadd (m := m) (n := n) a b => do
    let result := (← a.eval ctx env) + (← b.eval ctx env)
    scalarCast ctx (.uint (m + n)) result
  | .umul (m := m) (n := n) a b => do
    let result := (← a.eval ctx env) * (← b.eval ctx env)
    scalarCast ctx (.uint (m * n)) result
  | .usub (m := m) a b => do
    let a ← a.eval ctx env
    let b ← b.eval ctx env
    if a < b then throw "unsigned subtraction underflow"
    scalarCast ctx (.uint m) (a - b)
  | .cast (source := source) target value => do
    if target.isBytes || source.isBytes || target.isJubjub || source.isJubjub ||
        target.isForeign || source.isForeign then
      throw "byte strings and curve values do not support scalar conversion"
    scalarCast ctx target (← scalarNumber source (← value.eval ctx env))
  | .letE (source := source) name value body => do
    let value ← value.eval ctx env
    body.eval ctx ((name, Value.pack source value) :: env)
  | .assertE condition body => do
    unless (← condition.eval ctx env) do throw "helper assertion failed"
    body.eval ctx env
  | .copyValue value | .disclose _ value => value.eval ctx env
  | .eq (ty := ty) a b => do
    pure (sameValue ty (← a.eval ctx env) (← b.eval ctx env))
  | .select c a b => do
    let condition ← c.eval ctx env
    let yes ← a.eval ctx env
    let no ← b.eval ctx env
    pure (if condition then yes else no)
  | .poseidon2 domain a b => do
    if domain >= ctx.modulus then throw "noncanonical Poseidon domain"
    let value ← ctx.poseidon2 domain (← a.eval ctx env) (← b.eval ctx env)
    if value >= ctx.modulus then throw "hash oracle returned noncanonical value"
    pure value
  | .transientHash values => do
    if values.length > Types.defaultLimits.maxVectorLength then
      throw s!"transient_hash input count exceeds the maximum of {Types.defaultLimits.maxVectorLength}"
    let mut inputs := []
    for value in values do
      let field ← value.eval ctx env
      if field >= ctx.modulus then throw "noncanonical transient_hash Native input"
      inputs := inputs ++ [field]
    let result ← ctx.transientHash inputs
    if result >= ctx.modulus then throw "transient_hash oracle returned noncanonical value"
    pure result

theorem Expr.eval_reverseBytes32_twice (ctx : EvalContext) (env : EvalEnv)
    (value : Expr (.bytes 32)) :
    (Expr.reverseBytes32 (Expr.reverseBytes32 value)).eval ctx env = value.eval ctx env := by
  simp [Expr.eval]

theorem Expr.eval_reverseBytes_twice (ctx : EvalContext) (env : EvalEnv)
    (value : Expr (.bytes length)) :
    (Expr.reverseBytes (Expr.reverseBytes value)).eval ctx env = value.eval ctx env := by
  simp [Expr.eval]

/-- Check constraints in source order, preserving the first evaluation error. -/
def runConstraints (ctx : EvalContext) (env : EvalEnv) : List (Expr .bool) → Except String Unit
  | [] => .ok ()
  | condition :: rest =>
    match condition.eval ctx env with
    | .error message => .error message
    | .ok false => .error "circuit constraint failed"
    | .ok true => runConstraints ctx env rest

theorem disclose_evaluation (ctx : EvalContext) (env : EvalEnv) (span : SourceSpan) (value : Expr ty) :
    (Expr.disclose span value).eval ctx env = value.eval ctx env := by
  simp [Expr.eval]

private def evaluationCapabilities (ctx : EvalContext) : Capabilities :=
  {nativeModulus := ctx.modulus, typedBoolean := true, poseidon2 := true, persistentHash32 := true,
    persistentHashVector32 := true, persistentHashNative := true,
    sha512 := true, keccak256 := true,
    bytes32Conversions := true, hashToCurve := true, jubjub := true, foreignValues := true,
    foreignArithmetic := true, foreignByteConversions := true}

def Circuit.run (ctx : EvalContext) (c : Circuit) (env : EvalEnv) : Except String EvalEnv := do
  match c.validate (evaluationCapabilities ctx) with
  | .error diagnostic => throw diagnostic.message
  | .ok _ => pure ()
  if !uniqueNames (env.map Prod.fst) then throw "duplicate input value"
  for (name, _) in env do
    if !(c.inputs.any (·.name == name)) then throw s!"undeclared input value '{name}'"
  for input in c.inputs do
    let some raw := env.lookup input.name | throw s!"missing input '{input.name}'"
    let some value := raw.as input.ty | throw s!"input type mismatch for '{input.name}'"
    if !canonical ctx input.ty value then throw s!"noncanonical input '{input.name}'"
  runConstraints ctx env c.constraints
  c.outputs.mapM fun output => do
    pure (output.name, Value.pack output.ty (← output.value.eval ctx env))

/-- Pure transaction state. A failed transition returns no successor state. -/
structure LedgerState where
  cells : List (String × Value) := []
  maps : List (String × List (Value × Value)) := []
  trees : List (String × LedgerValue) := []
  events : List (EventKind × List Nat) := []
  shieldedMints : List (List Nat × Nat) := []
  unshieldedMints : List (List Nat × Nat) := []
  deriving Repr, BEq

/-- The source evaluator replaces an entry and places it first in the association list. -/
def updateAssoc [BEq α] (key : α) (value : β) (entries : List (α × β)) : List (α × β) :=
  (key, value) :: entries.filter (fun item => !(item.1 == key))

private def accumulateMintAmount (entries : List (List Nat × Nat))
    (domain : List Nat) (amount : Nat) : Except String (List (List Nat × Nat)) := do
  let total := (entries.lookup domain).getD 0 + amount
  unless total < 2 ^ 64 do throw "accumulated token effects exceed the native UInt64 sum"
  pure (updateAssoc domain total entries)

private def mintShielded (ctx : EvalContext) (env : EvalEnv) (state : LedgerState)
    (domain : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 64 - 1))) :
    Except String LedgerState := do
  let mints ← accumulateMintAmount state.shieldedMints
    (← domain.eval ctx env) (← amount.eval ctx env)
  pure {state with shieldedMints := mints}

private def mintUnshielded (ctx : EvalContext) (env : EvalEnv) (state : LedgerState)
    (domain : Expr (.bytes 32)) (amount : Expr (.uint (2 ^ 64 - 1))) :
    Except String LedgerState := do
  let mints ← accumulateMintAmount state.unshieldedMints
    (← domain.eval ctx env) (← amount.eval ctx env)
  pure {state with unshieldedMints := mints}

private def evaluatePath (ctx : EvalContext) (env : EvalEnv) (keys : List PathKey) :
    Except String (List Value) := keys.mapM fun key => match key with
  | .mk ty expression => do
    let value ← expression.eval ctx env
    if !canonical ctx ty value then throw "noncanonical nested map key"
    pure (Value.pack ty value)

private def treeLookup (root : LedgerValue) : List Value → Option LedgerValue
  | [] => some root
  | key :: rest => match root with
    | .scalar _ => none
    | .composite .. => none
    | .list _ => none
    | .map entries => (entries.lookup key).bind fun value => treeLookup value rest

private def treeMember (root : LedgerValue) (keys : List Value) : Except String Bool := do
  if keys.isEmpty then throw "nested membership path must contain at least one key"
  let parent ← match treeLookup root (keys.take (keys.length - 1)) with
    | some parent => pure parent
    | none => throw "nested membership parent is missing"
  let .map entries := parent | throw "nested membership parent is not a map"
  let some key := keys.getLast? | throw "nested membership path must contain at least one key"
  pure (entries.lookup key).isSome

private def treeSet (root : LedgerValue) (keys : List Value) (value : LedgerValue) :
    Option LedgerValue := do
  match keys with
  | [] => pure value
  | key :: rest =>
    match root with
    | .scalar _ => none
    | .composite .. => none
    | .list _ => none
    | .map entries =>
      if rest.isEmpty then
        pure (.map (updateAssoc key value entries))
      else do
        let child ← entries.lookup key
        let next ← treeSet child rest value
        pure (.map (updateAssoc key next entries))

/-- Remove a final map entry while preserving ancestor maps. A missing final key
is an unchanged map, matching the ledger VM's Map.remove behavior. -/
private def treeRemove (root : LedgerValue) : List Value → Option LedgerValue
  | [] => none
  | [key] => match root with
    | .map entries => some (.map (entries.filter fun (oldKey, _) => oldKey != key))
    | _ => none
  | key :: rest => match root with
    | .map entries => do
      let child ← entries.lookup key
      let updated ← treeRemove child rest
      pure (.map (updateAssoc key updated entries))
    | _ => none

private def counterValueAt (ctx : EvalContext) (root : LedgerValue)
    (keys : List Value) : Except String Nat := do
  let maximum := 2 ^ 64 - 1
  let some (.scalar raw) := treeLookup root keys
    | throw "missing nested Counter value"
  let some value := raw.as (.uint maximum)
    | throw "nested Counter value type mismatch"
  if !canonical ctx (.uint maximum) value then throw "noncanonical nested Counter value"
  pure value

private def adjustCounter (current amount : Nat) (subtract : Bool) : Except String Nat := do
  let maximum := 2 ^ 64 - 1
  if subtract then
    if current < amount then throw "Counter subtraction underflow"
    pure (current - amount)
  else
    if current > maximum - amount then throw "Counter addition overflow"
    pure (current + amount)

private def listPayloadAt (root : LedgerValue) (keys : List Value) :
    Except String (List (List Nat)) := do
  let some (.list entries) := treeLookup root keys
    | throw "missing or non-list state value"
  pure entries

/-- Execute ordered effects against a private tentative state and retain the
ordered read environment for expressions evaluated after the effects. Returning
an error never exposes that tentative state. -/
private def runEffectsWithEnv (ctx : EvalContext) (effects : List Effect) (env : EvalEnv)
    (state : LedgerState) : Except String (EvalEnv × LedgerState) := do
  let mut env := env
  let mut next := state
  for effect in effects do
    match effect with
    | .readCell name destination ty =>
      let some raw := next.cells.lookup name | throw s!"missing state cell '{name}'"
      let some value := raw.as ty | throw s!"state cell type mismatch '{name}'"
      if !canonical ctx ty value then throw s!"noncanonical state cell '{name}'"
      env := (destination, Value.pack ty value) :: env
    | .readMap name destination keyTy valueTy key =>
      let key := Value.pack keyTy (← key.eval ctx env)
      let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
      let some raw := entries.lookup key | throw s!"missing map key in '{name}'"
      let some value := raw.as valueTy | throw s!"state map value type mismatch '{name}'"
      if !canonical ctx valueTy value then throw s!"noncanonical state map value '{name}'"
      env := (destination, Value.pack valueTy value) :: env
    | .readMember name destination keyTy valueTy key =>
      let key := Value.pack keyTy (← key.eval ctx env)
      let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
      for (oldKey, oldValue) in entries do
        let some keyValue := oldKey.as keyTy | throw s!"state map key type mismatch '{name}'"
        let some value := oldValue.as valueTy | throw s!"state map value type mismatch '{name}'"
        if !canonical ctx keyTy keyValue || !canonical ctx valueTy value then
          throw s!"noncanonical state map entry '{name}'"
      env := (destination, Value.bool (entries.lookup key).isSome) :: env
    | .require condition =>
      if !(← condition.eval ctx env) then throw "state transition guard failed"
    | .claimContractCall .. =>
      throw "reference evaluator does not execute cross-contract claims"
    | .mintShielded domain amount =>
      next ← mintShielded ctx env next domain amount
    | .mintUnshielded domain amount =>
      next ← mintUnshielded ctx env next domain amount
    | .emitEvent kind payload =>
      next := {next with events := next.events ++ [(kind, ← payload.eval ctx env)]}
    | .requireContractCaller address =>
      unless ctx.contractCaller == some (← address.eval ctx env) do throw "required contract caller mismatch"
    | .writeCell name ty value =>
      let some existing := next.cells.lookup name | throw s!"missing state cell '{name}'"
      if (existing.as ty).isNone then throw s!"state cell type mismatch '{name}'"
      next := {next with cells := updateAssoc name (Value.pack ty (← value.eval ctx env)) next.cells}
    | .writeMap name keyTy valueTy key value =>
      let key := Value.pack keyTy (← key.eval ctx env)
      let value := Value.pack valueTy (← value.eval ctx env)
      let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
      for (oldKey, oldValue) in entries do
        if (oldKey.as keyTy).isNone || (oldValue.as valueTy).isNone then
          throw s!"state map type mismatch '{name}'"
      next := {next with maps := updateAssoc name (updateAssoc key value entries) next.maps}
    | .requireAbsent name keyTy key =>
      let key := Value.pack keyTy (← key.eval ctx env)
      let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
      if (entries.lookup key).isSome then throw "state map key already present"
    | .readPath name destination keys ty => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      let some (.scalar raw) := treeLookup root evaluated
        | throw s!"missing or non-scalar nested map value '{name}'"
      let some value := raw.as ty | throw s!"nested map value type mismatch '{name}'"
      if !canonical ctx ty value then throw s!"noncanonical nested map value '{name}'"
      env := (destination, Value.pack ty value) :: env
    | .readCompositePath name _ keys type destinations => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      let some (.composite found leaves) := treeLookup root evaluated
        | throw s!"missing or non-composite nested map value '{name}'"
      unless found == type && leaves.length == destinations.length do
        throw s!"nested composite state type mismatch '{name}'"
      unless leaves.all (· < ctx.modulus) do throw s!"noncanonical nested composite value '{name}'"
      env := env ++ (destinations.zip leaves).map fun (destination, value) =>
        (destination, .native value)
    | .memberPath name destination keys => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      env := (destination, .bool (← treeMember root evaluated)) :: env
    | .counterRead name destination keys => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive Counter state '{name}'"
      let value ← counterValueAt ctx root evaluated
      env := (destination, .uint (2 ^ 64 - 1) value) :: env
    | .counterAdjust name keys subtract amount => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive Counter state '{name}'"
      let current ← counterValueAt ctx root evaluated
      let value ← adjustCounter current amount subtract
      let some updated := treeSet root evaluated (.scalar (.uint (2 ^ 64 - 1) value))
        | throw s!"nested Counter parent is missing or not a map '{name}'"
      next := {next with trees := updateAssoc name updated next.trees}
    | .counterReset name keys => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive Counter state '{name}'"
      let some updated := treeSet root evaluated (.scalar (.uint (2 ^ 64 - 1) 0))
        | throw s!"nested Counter parent is missing or not a map '{name}'"
      next := {next with trees := updateAssoc name updated next.trees}
    | .listLength name destination keys => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive List state '{name}'"
      let entries ← listPayloadAt root evaluated
      let maximum := 2 ^ 64 - 1
      if entries.length > maximum then throw "List length exceeds u64"
      env := (destination, .uint maximum entries.length) :: env
    | .listHead name _ keys _type destinations => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive List state '{name}'"
      let entries ← listPayloadAt root evaluated
      let some leaves := entries.head? | throw "cannot read the head of an empty List"
      unless leaves.length == destinations.length do
        throw "List head record leaf count mismatch"
      unless leaves.all (· < ctx.modulus) do throw "noncanonical List record field"
      env := env ++ (destinations.zip leaves).map fun (destination, value) =>
        (destination, .native value)
    | .listPushFront name keys _type values => do
      let evaluated ← evaluatePath ctx env keys
      let leaves ← values.mapM fun value => do
        let result ← value.eval ctx env
        if result ≥ ctx.modulus then throw "noncanonical List record field"
        pure result
      if leaves.isEmpty then throw "List record must contain at least one field"
      let some root := next.trees.lookup name | throw s!"missing recursive List state '{name}'"
      let entries ← listPayloadAt root evaluated
      let maximum := 2 ^ 64 - 1
      if entries.length ≥ maximum then throw "List length overflow"
      let some updated := treeSet root evaluated (.list (leaves :: entries))
        | throw s!"nested List parent is missing or not a map '{name}'"
      next := {next with trees := updateAssoc name updated next.trees}
    | .listPopFront name keys => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive List state '{name}'"
      let entries ← listPayloadAt root evaluated
      let rest ← match entries with
        | [] => throw "cannot pop from an empty List"
        | _ :: rest => pure rest
      let some updated := treeSet root evaluated (.list rest)
        | throw s!"nested List parent is missing or not a map '{name}'"
      next := {next with trees := updateAssoc name updated next.trees}
    | .listReset name keys => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive List state '{name}'"
      let some updated := treeSet root evaluated (.list [])
        | throw s!"nested List parent is missing or not a map '{name}'"
      next := {next with trees := updateAssoc name updated next.trees}
    | .insertPath name keys ty value | .writePath name keys ty value => do
      let evaluated ← evaluatePath ctx env keys
      let payload := LedgerValue.scalar (Value.pack ty (← value.eval ctx env))
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      let some updated := treeSet root evaluated payload
        | throw s!"nested map parent is missing or not a map '{name}'"
      next := {next with trees := updateAssoc name updated next.trees}
    | .writeCompositePath name keys type values => do
      let evaluated ← evaluatePath ctx env keys
      let leaves ← values.mapM (fun value => value.eval ctx env)
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      let some updated := treeSet root evaluated (.composite type leaves)
        | throw s!"nested map parent is missing or not a map '{name}'"
      next := {next with trees := updateAssoc name updated next.trees}
    | .emptyMapPath name keys => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      let some updated := treeSet root evaluated (.map [])
        | throw s!"nested map parent is missing or not a map '{name}'"
      next := {next with trees := updateAssoc name updated next.trees}
    | .removePath name keys => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      let some updated := treeRemove root evaluated
        | throw s!"nested map parent is missing or not a map '{name}'"
      next := {next with trees := updateAssoc name updated next.trees}
  pure (env, next)

/-- Execute ordered effects while preserving the historical state-only result. -/
def runEffects (ctx : EvalContext) (effects : List Effect) (env : EvalEnv)
    (state : LedgerState) : Except String LedgerState := do
  let (_, next) ← runEffectsWithEnv ctx effects env state
  pure next

/-- Execute source effects with optional scalar read/write and require guards.
Inactive reads bind their canonical zero without touching state or keys.
Retain the resulting environment for returns and source-level proofs. -/
def runEffectsWithGuardsAndEnv (ctx : EvalContext) (effects : List Effect)
    (guards : List (Option (Expr .bool))) (env : EvalEnv)
    (state : LedgerState) : Except String (EvalEnv × LedgerState) := do
  unless guards.isEmpty || guards.length == effects.length do
    throw "effect guard metadata length mismatch"
  if guards.isEmpty then
    runEffectsWithEnv ctx effects env state
  else do
    let mut env := env
    let mut next := state
    for (effect, index) in effects.zipIdx do
      let guard := guards[index]?.getD none
      if guard.isSome then
        match effect with
        | .readCell .. | .readMap .. | .readMember .. | .writeCell .. | .writeMap .. | .require .. |
            .readPath .. | .readCompositePath .. | .memberPath .. | .insertPath .. |
            .writePath .. | .writeCompositePath .. | .emptyMapPath .. | .counterRead .. |
            .counterAdjust .. | .counterReset .. | .removePath .. |
            .claimContractCall .. | .mintShielded .. | .mintUnshielded .. |
            .requireContractCaller .. | .emitEvent .. => pure ()
        | _ => throw "native guards are supported only on ledger reads, writes, and require effects"
      let active ← match guard with
        | some condition => condition.eval ctx env
        | _ => pure true
      if active then
        match effect with
        | .readCell name destination ty =>
          let some raw := next.cells.lookup name | throw s!"missing state cell '{name}'"
          let some value := raw.as ty | throw s!"state cell type mismatch '{name}'"
          if !canonical ctx ty value then throw s!"noncanonical state cell '{name}'"
          env := (destination, Value.pack ty value) :: env
        | .readMap name destination keyTy valueTy key =>
          let key := Value.pack keyTy (← key.eval ctx env)
          let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
          let some raw := entries.lookup key | throw s!"missing map key in '{name}'"
          let some value := raw.as valueTy | throw s!"state map value type mismatch '{name}'"
          if !canonical ctx valueTy value then throw s!"noncanonical state map value '{name}'"
          env := (destination, Value.pack valueTy value) :: env
        | .readMember name destination keyTy valueTy key =>
          let key := Value.pack keyTy (← key.eval ctx env)
          let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
          for (oldKey, oldValue) in entries do
            let some keyValue := oldKey.as keyTy | throw s!"state map key type mismatch '{name}'"
            let some value := oldValue.as valueTy | throw s!"state map value type mismatch '{name}'"
            if !canonical ctx keyTy keyValue || !canonical ctx valueTy value then
              throw s!"noncanonical state map entry '{name}'"
          env := (destination, Value.bool (entries.lookup key).isSome) :: env
        | .require condition =>
          if !(← condition.eval ctx env) then throw "state transition guard failed"
        | .claimContractCall .. =>
          throw "reference evaluator does not execute cross-contract claims"
        | .mintShielded domain amount =>
          next ← mintShielded ctx env next domain amount
        | .mintUnshielded domain amount =>
          next ← mintUnshielded ctx env next domain amount
        | .emitEvent kind payload =>
          next := {next with events := next.events ++ [(kind, ← payload.eval ctx env)]}
        | .requireContractCaller address =>
          unless ctx.contractCaller == some (← address.eval ctx env) do throw "required contract caller mismatch"
        | .writeCell name ty value =>
          let some existing := next.cells.lookup name | throw s!"missing state cell '{name}'"
          if (existing.as ty).isNone then throw s!"state cell type mismatch '{name}'"
          next := {next with cells := updateAssoc name (Value.pack ty (← value.eval ctx env)) next.cells}
        | .writeMap name keyTy valueTy key value =>
          let key := Value.pack keyTy (← key.eval ctx env)
          let value := Value.pack valueTy (← value.eval ctx env)
          let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
          for (oldKey, oldValue) in entries do
            if (oldKey.as keyTy).isNone || (oldValue.as valueTy).isNone then
              throw s!"state map type mismatch '{name}'"
          next := {next with maps := updateAssoc name (updateAssoc key value entries) next.maps}
        | .requireAbsent name keyTy key =>
          let key := Value.pack keyTy (← key.eval ctx env)
          let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
          if (entries.lookup key).isSome then throw "state map key already present"
        | .readPath name destination keys ty => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          let some (.scalar raw) := treeLookup root evaluated
            | throw s!"missing or non-scalar nested map value '{name}'"
          let some value := raw.as ty | throw s!"nested map value type mismatch '{name}'"
          if !canonical ctx ty value then throw s!"noncanonical nested map value '{name}'"
          env := (destination, Value.pack ty value) :: env
        | .readCompositePath name _ keys type destinations => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          let some (.composite found leaves) := treeLookup root evaluated
            | throw s!"missing or non-composite nested map value '{name}'"
          unless found == type && leaves.length == destinations.length do
            throw s!"nested composite state type mismatch '{name}'"
          unless leaves.all (· < ctx.modulus) do throw s!"noncanonical nested composite value '{name}'"
          env := env ++ (destinations.zip leaves).map fun (destination, value) =>
            (destination, .native value)
        | .memberPath name destination keys => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          env := (destination, .bool (← treeMember root evaluated)) :: env
        | .counterRead name destination keys => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive Counter state '{name}'"
          let value ← counterValueAt ctx root evaluated
          env := (destination, .uint (2 ^ 64 - 1) value) :: env
        | .counterAdjust name keys subtract amount => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive Counter state '{name}'"
          let current ← counterValueAt ctx root evaluated
          let value ← adjustCounter current amount subtract
          let some updated := treeSet root evaluated (.scalar (.uint (2 ^ 64 - 1) value))
            | throw s!"nested Counter parent is missing or not a map '{name}'"
          next := {next with trees := updateAssoc name updated next.trees}
        | .counterReset name keys => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive Counter state '{name}'"
          let some updated := treeSet root evaluated (.scalar (.uint (2 ^ 64 - 1) 0))
            | throw s!"nested Counter parent is missing or not a map '{name}'"
          next := {next with trees := updateAssoc name updated next.trees}
        | .listLength name destination keys => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive List state '{name}'"
          let entries ← listPayloadAt root evaluated
          let maximum := 2 ^ 64 - 1
          if entries.length > maximum then throw "List length exceeds u64"
          env := (destination, .uint maximum entries.length) :: env
        | .listHead name _ keys _type destinations => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive List state '{name}'"
          let entries ← listPayloadAt root evaluated
          let some leaves := entries.head? | throw "cannot read the head of an empty List"
          unless leaves.length == destinations.length do
            throw "List head record leaf count mismatch"
          unless leaves.all (· < ctx.modulus) do throw "noncanonical List record field"
          env := env ++ (destinations.zip leaves).map fun (destination, value) =>
            (destination, .native value)
        | .listPushFront name keys _type values => do
          let evaluated ← evaluatePath ctx env keys
          let leaves ← values.mapM fun value => do
            let result ← value.eval ctx env
            if result ≥ ctx.modulus then throw "noncanonical List record field"
            pure result
          if leaves.isEmpty then throw "List record must contain at least one field"
          let some root := next.trees.lookup name | throw s!"missing recursive List state '{name}'"
          let entries ← listPayloadAt root evaluated
          let maximum := 2 ^ 64 - 1
          if entries.length ≥ maximum then throw "List length overflow"
          let some updated := treeSet root evaluated (.list (leaves :: entries))
            | throw s!"nested List parent is missing or not a map '{name}'"
          next := {next with trees := updateAssoc name updated next.trees}
        | .listPopFront name keys => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive List state '{name}'"
          let entries ← listPayloadAt root evaluated
          let rest ← match entries with
            | [] => throw "cannot pop from an empty List"
            | _ :: rest => pure rest
          let some updated := treeSet root evaluated (.list rest)
            | throw s!"nested List parent is missing or not a map '{name}'"
          next := {next with trees := updateAssoc name updated next.trees}
        | .listReset name keys => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive List state '{name}'"
          let some updated := treeSet root evaluated (.list [])
            | throw s!"nested List parent is missing or not a map '{name}'"
          next := {next with trees := updateAssoc name updated next.trees}
        | .insertPath name keys ty value | .writePath name keys ty value => do
          let evaluated ← evaluatePath ctx env keys
          let payload := LedgerValue.scalar (Value.pack ty (← value.eval ctx env))
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          let some updated := treeSet root evaluated payload
            | throw s!"nested map parent is missing or not a map '{name}'"
          next := {next with trees := updateAssoc name updated next.trees}
        | .writeCompositePath name keys type values => do
          let evaluated ← evaluatePath ctx env keys
          let leaves ← values.mapM (fun value => value.eval ctx env)
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          let some updated := treeSet root evaluated (.composite type leaves)
            | throw s!"nested map parent is missing or not a map '{name}'"
          next := {next with trees := updateAssoc name updated next.trees}
        | .emptyMapPath name keys => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          let some updated := treeSet root evaluated (.map [])
            | throw s!"nested map parent is missing or not a map '{name}'"
          next := {next with trees := updateAssoc name updated next.trees}
        | .removePath name keys => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          let some updated := treeRemove root evaluated
            | throw s!"nested map parent is missing or not a map '{name}'"
          next := {next with trees := updateAssoc name updated next.trees}
      else
        match effect with
        | .readCell _ destination ty =>
          let zero : ty.Denote := match ty with
            | .native => 0
            | .bool => false
            | .uint _ => 0
            | .bytes length => List.replicate length 0
            | .jubjubScalar => 0
            | .jubjubPoint => (0, 1)
            | .foreign (.base _) | .foreign (.scalar _) => 0
            | .foreign (.point _) => .identity
          env := (destination, Value.pack ty zero) :: env
        | .readMap _ destination _ ty _ =>
          let zero : ty.Denote := match ty with
            | .native => 0
            | .bool => false
            | .uint _ => 0
            | .bytes length => List.replicate length 0
            | .jubjubScalar => 0
            | .jubjubPoint => (0, 1)
            | .foreign (.base _) | .foreign (.scalar _) => 0
            | .foreign (.point _) => .identity
          env := (destination, Value.pack ty zero) :: env
        | .readMember _ destination .. =>
          env := (destination, .bool false) :: env
        | .writeCell .. | .writeMap .. | .require .. | .claimContractCall .. |
            .mintShielded .. | .mintUnshielded .. |
            .requireContractCaller .. | .emitEvent .. |
            .insertPath .. | .writePath .. |
            .writeCompositePath .. | .emptyMapPath .. | .listPushFront .. |
            .listPopFront .. | .listReset .. | .removePath .. => pure ()
        | .readPath _ destination _ ty =>
          let zero : ty.Denote := match ty with
            | .native => 0
            | .bool => false
            | .uint _ => 0
            | .bytes length => List.replicate length 0
            | .jubjubScalar => 0
            | .jubjubPoint => (0, 1)
            | .foreign (.base _) | .foreign (.scalar _) => 0
            | .foreign (.point _) => .identity
          env := (destination, Value.pack ty zero) :: env
        | .readCompositePath _ _ _ _ destinations =>
          env := env ++ destinations.map fun destination => (destination, .native 0)
        | .memberPath _ destination _ => env := (destination, .bool false) :: env
        | .counterRead _ destination _ => env := (destination, .uint (2 ^ 64 - 1) 0) :: env
        | .counterAdjust .. | .counterReset .. => pure ()
        | .listLength _ destination _ => env := (destination, .uint (2 ^ 64 - 1) 0) :: env
        | .listHead _ _ _ _ destinations =>
          env := env ++ destinations.map fun destination => (destination, .native 0)
        | _ => throw "native guards are supported only on ledger reads, writes, and require effects"
    pure (env, next)

/-- Guarded state transition with the original state-only result type. -/
def runEffectsWithGuards (ctx : EvalContext) (effects : List Effect)
    (guards : List (Option (Expr .bool))) (env : EvalEnv)
    (state : LedgerState) : Except String LedgerState := do
  let (_, next) ← runEffectsWithGuardsAndEnv ctx effects guards env state
  pure next

/-- This is a specification evaluator, not a substitute for ledger proof checks. -/
def Entrypoint.run (ctx : EvalContext) (entry : Entrypoint) (env : EvalEnv)
    (state : LedgerState) : Except String (EvalEnv × LedgerState) := do
  match Disclosure.entrypoint entry with
  | .error diagnostic => throw diagnostic.message
  | .ok _ => pure ()
  let outputs ← entry.circuit.run ctx env
  let (finalEnv, next) ←
    runEffectsWithGuardsAndEnv ctx entry.effects entry.effectGuards (outputs ++ env) state
  let returned ← entry.returns.mapM fun output => do
    let value ← output.value.eval ctx finalEnv
    if !canonical ctx output.ty value then throw s!"noncanonical entrypoint return '{output.name}'"
    pure (output.name, Value.pack output.ty value)
  pure (outputs ++ returned, next)

/-- A small optimization whose correctness does not depend on the backend or hash. -/
def pruneTrue : List (Expr .bool) → List (Expr .bool)
  | [] => []
  | .bool true :: rest => pruneTrue rest
  | condition :: rest => condition :: pruneTrue rest

def ConstraintsHold (ctx : EvalContext) (env : EvalEnv) : List (Expr .bool) → Prop
  | [] => True
  | condition :: rest => condition.eval ctx env = .ok true ∧ ConstraintsHold ctx env rest

theorem pruneTrue_preserves (ctx : EvalContext) (env : EvalEnv) (conditions : List (Expr .bool)) :
    ConstraintsHold ctx env (pruneTrue conditions) ↔ ConstraintsHold ctx env conditions := by
  induction conditions with
  | nil => rfl
  | cons condition rest ih =>
    cases condition with
    | bool b => cases b <;> simp [pruneTrue, ConstraintsHold, Expr.eval, ih]
    | boolAnd left right => simp [pruneTrue, ConstraintsHold, ih]
    | boolOr left right => simp [pruneTrue, ConstraintsHold, ih]
    | boolXor left right => simp [pruneTrue, ConstraintsHold, ih]
    | copyValue value => simp [pruneTrue, ConstraintsHold, ih]
    | ref name => simp [pruneTrue, ConstraintsHold, ih]
    | eq a b => simp [pruneTrue, ConstraintsHold, ih]
    | select condition a b => simp [pruneTrue, ConstraintsHold, ih]
    | cast target value => simp [pruneTrue, ConstraintsHold, ih]
    | letE name value body => simp [pruneTrue, ConstraintsHold, ih]
    | assertE condition body => simp [pruneTrue, ConstraintsHold, ih]
    | disclose span value => simp [pruneTrue, ConstraintsHold, ih]
    | inv value => simp [pruneTrue, ConstraintsHold, ih]
    | fromBytes32 value => simp [pruneTrue, ConstraintsHold, Expr.eval, ih]
    | fromBytes value => simp [pruneTrue, ConstraintsHold, Expr.eval, ih]

theorem unsigned_addition_no_wrap (a b m n : Nat) (ha : a ≤ m) (hb : b ≤ n)
    (hbound : m + n ≤ ScalarPolicy.maxUint) : (a + b) % Field.modulus = a + b :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
    (Nat.le_trans (ScalarPolicy.addition_range a b m n ha hb) hbound)
    ScalarPolicy.maxUint_lt_native)

theorem unsigned_multiplication_no_wrap (a b m n : Nat) (ha : a ≤ m) (hb : b ≤ n)
    (hbound : m * n ≤ ScalarPolicy.maxUint) : (a * b) % Field.modulus = a * b :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
    (Nat.le_trans (ScalarPolicy.multiplication_range a b m n ha hb) hbound)
    ScalarPolicy.maxUint_lt_native)

/-- An underflowed field subtraction lies above every supported unsigned bound. -/
theorem unsigned_underflow_outside_range (a b : Nat) (_hab : a < b)
    (hb : b ≤ ScalarPolicy.maxUint) : ScalarPolicy.maxUint < Field.modulus + a - b := by
  have hseparation : 2 * ScalarPolicy.maxUint < Field.modulus := by decide
  omega

theorem unsigned_underflow_modulo_rejected (a b : Nat) (hab : a < b)
    (hb : b ≤ ScalarPolicy.maxUint) :
    ScalarPolicy.maxUint < (Field.modulus + a - b) % Field.modulus := by
  have hfield := ScalarPolicy.maxUint_lt_native
  have hbelow : Field.modulus + a - b < Field.modulus := by omega
  rw [Nat.mod_eq_of_lt hbelow]
  exact unsigned_underflow_outside_range a b hab hb

end Noctium
