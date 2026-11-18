import Noctium.IR

namespace Noctium.GuardedExpression

private def zeroValue : (ty : Ty) → Option (Expr ty)
  | .native => some (.native 0)
  | .bool => some (.bool false)
  | .uint maximum => some (.uint maximum 0)
  | .bytes 32 => some (.bytes32Literal (List.replicate 32 0))
  | .bytes length => some (.bytesLiteral length (List.replicate length 0))
  | .jubjubScalar => some (.jubjubScalarFromNative (.native 0))
  | .jubjubPoint => some (.jubjubFromCoordinates (.native 0) (.native 1))
  | .foreign (.base curve) => some (.foreignBase curve 0)
  | .foreign (.scalar curve) => some (.foreignScalar curve 0)
  | .foreign (.point curve) => some (.foreignIdentity curve)

private def castMayFail (target source : Ty) : Bool :=
  match target, source with
  | .uint _, .native => true
  | .uint maximum, .uint sourceMaximum => sourceMaximum > maximum
  | .uint maximum, .bool => maximum < 1
  | _, _ => false

private def foreignFieldOne : (field : Foreign.FieldKind) → Expr (.foreign field.kind)
  | .base curve => .foreignBase curve 1
  | .scalar curve => .foreignScalar curve 1

private def safeForeignPoint (curve : Foreign.Curve) : Expr (.foreign (.point curve)) :=
  .foreignUnary (.mulGenerator curve) (.foreignScalar curve 1)

/-- Guard insertion is nonrecursive. The traversal below recurses only on
original expression children, before these safe operands are introduced. -/
private def guardForeignUnary (guard : Expr .bool) : (op : Foreign.UnaryOp) →
    Expr (.foreign op.inputKind) → Expr (.foreign op.outputKind)
  | .inv field, value =>
    .foreignUnary (.inv field) (.select guard value (foreignFieldOne field))
  | .x .curve25519, value => .foreignUnary (.x .curve25519) value
  | .y .curve25519, value => .foreignUnary (.y .curve25519) value
  | .x curve, value =>
    .foreignUnary (.x curve) (.select guard value (safeForeignPoint curve))
  | .y curve, value =>
    .foreignUnary (.y curve) (.select guard value (safeForeignPoint curve))
  | op, value => .foreignUnary op value

private def guardForeignBinary (guard : Expr .bool) : (op : Foreign.BinaryOp) →
    Expr (.foreign op.leftKind) → Expr (.foreign op.rightKind) → Expr (.foreign op.outputKind)
  | .fromCoordinates curve, left, right =>
    .foreignBinary (.fromCoordinates curve)
      (.select guard left (.foreignUnary (.x curve) (safeForeignPoint curve)))
      (.select guard right (.foreignUnary (.y curve) (safeForeignPoint curve)))
  | op, left, right => .foreignBinary op left right

private def guardForeignFromBytes (guard : Expr .bool) : (kind : Foreign.Kind) →
    {length : Nat} → Expr (.bytes length) → Expr (.foreign kind)
  | .point .secp256k1, 33, value =>
    .foreignFromBytes (.point .secp256k1) (.select guard value (.bytesLiteral 33 (List.replicate 33 0)))
  | .point .secp256r1, 33, value =>
    .foreignFromBytes (.point .secp256r1) (.select guard value (.bytesLiteral 33 (List.replicate 33 0)))
  | .point .curve25519, 32, value =>
    .foreignFromBytes (.point .curve25519)
      (.select guard value (.bytesLiteral 32 (1 :: List.replicate 31 0)))
  | kind, _, value => .foreignFromBytes kind value

/-- Replace every partial scalar operation with a safe inactive computation.
The caller supplies a stable guard expression, usually a fresh outer let
reference, so nested source lets cannot capture it. Eager selects still
evaluate both arms. -/
def totalize (guard : Expr .bool) : Expr ty → Expr ty
  | .foreignBase curve value => .foreignBase curve value
  | .foreignScalar curve value => .foreignScalar curve value
  | .foreignIdentity curve => .foreignIdentity curve
  | .foreignEncodedField value index => .foreignEncodedField (totalize guard value) index
  | .foreignUnary op value => guardForeignUnary guard op (totalize guard value)
  | .foreignBinary op left right =>
    guardForeignBinary guard op (totalize guard left) (totalize guard right)
  | .foreignToBytes value => .foreignToBytes (totalize guard value)
  | .foreignFromBytes kind value => guardForeignFromBytes guard kind (totalize guard value)
  | .native value => .native value
  | .bool value => .bool value
  | .boolAnd left right => .boolAnd (totalize guard left) (totalize guard right)
  | .boolOr left right => .boolOr (totalize guard left) (totalize guard right)
  | .boolXor left right => .boolXor (totalize guard left) (totalize guard right)
  | .uint maximum value => .uint maximum value
  | .bytesField value index => .bytesField (totalize guard value) index
  | .bytesAt value index => .bytesAt (totalize guard value) index
  | .sha512 value => .sha512 (totalize guard value)
  | .keccak256 value => .keccak256 (totalize guard value)
  | .persistentHash32 value => .persistentHash32 (totalize guard value)
  | .bytes32Literal values => .bytes32Literal values
  | .bytesLiteral length values => .bytesLiteral length values
  | .reverseBytes value => .reverseBytes (totalize guard value)
  | .sliceBytes value start end_ => .sliceBytes (totalize guard value) start end_
  | .concatBytes left right => .concatBytes (totalize guard left) (totalize guard right)
  | .persistentHashVector32 values => .persistentHashVector32 (values.map (totalize guard))
  | .persistentHashNative value => .persistentHashNative (totalize guard value)
  | .persistentHashNativeVector values => .persistentHashNativeVector (values.map (totalize guard))
  | .transientHash values => .transientHash (values.map (totalize guard))
  | .hashToCurve values => .hashToCurve (values.map (totalize guard))
  | .toBytes32 value => .toBytes32 (totalize guard value)
  | .reverseBytes32 value => .reverseBytes32 (totalize guard value)
  | .fromBytes32 (target := .jubjubPoint) value =>
    let identity : Expr (.bytes 32) := .bytes32Literal (1 :: List.replicate 31 0)
    .fromBytes32 (.select guard (totalize guard value) identity)
  | .fromBytes32 value => .fromBytes32 (totalize guard value)
  | .fromBytes value => .fromBytes (totalize guard value)
  | .jubjubScalarFromNative value => .jubjubScalarFromNative (totalize guard value)
  | .jubjubScalarToNative value => .jubjubScalarToNative (totalize guard value)
  | .jubjubMulGenerator scalar => .jubjubMulGenerator (totalize guard scalar)
  | .jubjubMul point scalar =>
    .jubjubMul (totalize guard point) (totalize guard scalar)
  | .jubjubAdd left right =>
    .jubjubAdd (totalize guard left) (totalize guard right)
  | .jubjubNeg point => .jubjubNeg (totalize guard point)
  | .jubjubCoordinate point index => .jubjubCoordinate (totalize guard point) index
  | .jubjubFromCoordinates x y => .jubjubFromCoordinates
      (.select guard (totalize guard x) (.native 0))
      (.select guard (totalize guard y) (.native 1))
  | .ref name => .ref name
  | .add left right => .add (totalize guard left) (totalize guard right)
  | .mul left right => .mul (totalize guard left) (totalize guard right)
  | .sub left right => .sub (totalize guard left) (totalize guard right)
  | .uadd left right => .uadd (totalize guard left) (totalize guard right)
  | .usub (m := m) (n := n) left right =>
    .usub
      (.select guard (totalize guard left) (.uint m 0))
      (.select guard (totalize guard right) (.uint n 0))
  | .umul left right => .umul (totalize guard left) (totalize guard right)
  | .inv (ty := .native) value =>
    .inv (.select guard (totalize guard value) (.native 1))
  | .inv (ty := .jubjubScalar) value =>
    .inv (.jubjubScalarFromNative
      (.select guard (.jubjubScalarToNative (totalize guard value)) (.native 1)))
  | .inv value => .inv (totalize guard value)
  | .cast target (source := source) value =>
    let value := totalize guard value
    if castMayFail target source then
      match zeroValue source with
      | some zero => .cast target (.select guard value zero)
      | none => .cast target value
    else .cast target value
  | .letE name value body =>
    .letE name (totalize guard value) (totalize guard body)
  | .assertE condition body =>
    .assertE (.select guard (totalize guard condition) (.bool true))
      (totalize guard body)
  | .disclose span value => .disclose span (totalize guard value)
  | .eq left right => .eq (totalize guard left) (totalize guard right)
  | .select condition yes no =>
    .select (totalize guard condition) (totalize guard yes) (totalize guard no)
  | .poseidon2 domain left right =>
    .poseidon2 domain (totalize guard left) (totalize guard right)

end Noctium.GuardedExpression
