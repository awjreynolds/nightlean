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

end Noctium.Foreign
