import Noctium.Field

namespace Noctium.Foreign

inductive Curve where
  | secp256k1 | secp256r1
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Kind where
  | base (curve : Curve)
  | scalar (curve : Curve)
  | point (curve : Curve)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Logical points do not expose their five native wire fields. -/
inductive Point where
  | identity
  | affine (x y : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

abbrev Kind.Denote : Kind → Type
  | .base _ | .scalar _ => Nat
  | .point _ => Point

instance (kind : Kind) : BEq kind.Denote := by
  cases kind <;> simp only [Kind.Denote] <;> infer_instance

instance (kind : Kind) : DecidableEq kind.Denote := by
  cases kind <;> simp only [Kind.Denote] <;> infer_instance

def Curve.name : Curve → String
  | .secp256k1 => "Secp256k1"
  | .secp256r1 => "Secp256r1"

/-- Moduli from the pinned midnight-curves 0.3.1 k256/p256 field types. -/
def Curve.baseModulus : Curve → Nat
  | .secp256k1 => 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffc2f
  | .secp256r1 => 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff

def Curve.scalarModulus : Curve → Nat
  | .secp256k1 => 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
  | .secp256r1 => 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551

def Curve.coefficientA : Curve → Nat
  | .secp256k1 => 0
  | .secp256r1 => Curve.baseModulus .secp256r1 - 3

def Curve.coefficientB : Curve → Nat
  | .secp256k1 => 7
  | .secp256r1 => 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b

def Kind.curve : Kind → Curve
  | .base curve | .scalar curve | .point curve => curve

def Kind.nativeName : Kind → String
  | .base curve => s!"Base<{curve.name}>"
  | .scalar curve => s!"Scalar<{curve.name}>"
  | .point curve => s!"Point<{curve.name}>"

def Kind.sourceName : Kind → String
  | .base curve => curve.name ++ "Base"
  | .scalar curve => curve.name ++ "Scalar"
  | .point curve => curve.name ++ "Point"

def Kind.encodedFieldCount : Kind → Nat
  | .base _ | .scalar _ => 2
  | .point _ => 5

def Kind.byteLength : Kind → Nat
  | .base _ | .scalar _ => 32
  | .point _ => 33

def Kind.modulus? : Kind → Option Nat
  | .base curve => some curve.baseModulus
  | .scalar curve => some curve.scalarModulus
  | .point _ => none

def kinds : List Kind := [
  .point .secp256k1, .base .secp256k1, .scalar .secp256k1,
  .point .secp256r1, .base .secp256r1, .scalar .secp256r1]

def lowRadix : Nat := 2 ^ 192
def highRadix : Nat := 2 ^ 64

/-- Canonical native Encode uses x-1 modulo the selected foreign field. -/
def encodeField (kind : Kind) (value : Nat) : Except String (List Nat) := do
  let some modulus := kind.modulus? | throw "foreign point requires a point encoding"
  unless value < modulus do throw "foreign field value is not canonical"
  let shifted := (value + modulus - 1) % modulus
  pure [shifted % lowRadix, shifted / lowRadix]

/-- Exact inverse of canonical field encoding, with both limb and range checks. -/
def decodeField (kind : Kind) (encoding : List Nat) : Except String Nat := do
  let some modulus := kind.modulus? | throw "foreign point requires a point decoding"
  let [low, high] := encoding | throw "foreign field encoding requires two limbs"
  unless low < lowRadix && high < highRadix do throw "foreign field limb is out of range"
  let shifted := low + lowRadix * high
  unless shifted < modulus do throw "foreign field encoding is not canonical"
  pure ((shifted + 1) % modulus)

/-- Secp identity uses two canonical encodings of base-field zero and flag one. -/
def identityEncoding (curve : Curve) : List Nat :=
  let shifted := curve.baseModulus - 1
  let low := shifted % lowRadix
  let high := shifted / lowRadix
  [low, high, low, high, 1]

/-- Canonical curve membership for the two pinned cofactor-one Secp curves. -/
def pointValid (curve : Curve) : Point → Bool
  | .identity => true
  | .affine x y => Id.run do
    let p := curve.baseModulus
    if x >= p || y >= p then return false
    let lhs := y * y % p
    let rhs := (x * x % p * x + curve.coefficientA * x + curve.coefficientB) % p
    return lhs == rhs

def Kind.canonical : (kind : Kind) → kind.Denote → Bool
  | .base curve, value => value < curve.baseModulus
  | .scalar curve, value => value < curve.scalarModulus
  | .point curve, value => pointValid curve value

/-- Canonical native Encode for the logical point representation. Affine
coordinates use the base field's two limbs, followed by a zero identity flag.
The distinguished identity uses zero encodings and flag one. -/
def encodePoint (curve : Curve) (point : Point) : Except String (List Nat) := do
  unless pointValid curve point do throw "foreign point is not canonical or on curve"
  match point with
  | .identity => pure (identityEncoding curve)
  | .affine x y => do
    let xFields ← encodeField (.base curve) x
    let yFields ← encodeField (.base curve) y
    pure (xFields ++ yFields ++ [0])

/-- Decode the five field representation, requiring exact flags, canonical
field limbs, and a valid affine point. -/
def decodePoint (curve : Curve) (encoding : List Nat) : Except String Point := do
  let [xLow, xHigh, yLow, yHigh, flag] := encoding
    | throw "foreign point encoding requires five fields"
  unless flag ≤ 1 do throw "foreign point identity flag must be zero or one"
  let x ← decodeField (.base curve) [xLow, xHigh]
  let y ← decodeField (.base curve) [yLow, yHigh]
  if flag == 1 then
    unless x == 0 && y == 0 do throw "foreign identity encoding has nonzero coordinates"
    pure .identity
  else do
    let point := .affine x y
    unless pointValid curve point do throw "foreign point is not on curve"
    pure point

def encodeValue : (kind : Kind) → kind.Denote → Except String (List Nat)
  | .base curve, value => do
    unless value < curve.baseModulus do throw "foreign value is not canonical"
    encodeField (.base curve) value
  | .scalar curve, value => do
    unless value < curve.scalarModulus do throw "foreign value is not canonical"
    encodeField (.scalar curve) value
  | .point curve, value => encodePoint curve value

def decodeValue : (kind : Kind) → List Nat → Except String kind.Denote
  | .base curve, encoding => decodeField (.base curve) encoding
  | .scalar curve, encoding => decodeField (.scalar curve) encoding
  | .point curve, encoding => decodePoint curve encoding

end Noctium.Foreign
