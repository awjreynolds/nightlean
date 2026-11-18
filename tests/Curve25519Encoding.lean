import Noctium.Foreign

open Noctium.Foreign

private def curve := Curve.curve25519
private def p := curve.baseModulus
private def l := curve.scalarModulus
private def generatorX :=
  15112221349535400772501151409588531511454012693041857206046113283949847762202
private def generatorY :=
  46316835694926478169428394003475163141307993866256225615783033603165251855960
private def generator : Point := .affine generatorX generatorY
private def generatorPlusOrderTwo : Point := .affine (p - generatorX) (p - generatorY)

private def rejected (value : Except String α) : Bool := !value.isOk

#guard curve.name == "Curve25519"
#guard (Kind.base curve).nativeName == "Base<Curve25519>"
#guard (Kind.scalar curve).sourceName == "Curve25519Scalar"
#guard (Kind.point curve).encodedFieldCount == 4 && (Kind.point curve).byteLength == 32
#guard (Kind.scalar curve).lowRadix == 2 ^ 204 && (Kind.base curve).lowRadix == lowRadix
#guard p == 2 ^ 255 - 19
#guard l == 2 ^ 252 + 27742317777372353535851937790883648493
#guard [0, 1, p - 1].all fun value =>
  (encodeField (.base curve) value >>= decodeField (.base curve)).toOption == some value
#guard [0, 1, l - 1].all fun value =>
  (encodeField (.scalar curve) value >>= decodeField (.scalar curve)).toOption == some value
#guard (encodeField (.scalar curve) 0).toOption ==
  some [((l - 1) % (2 ^ 204)), ((l - 1) / (2 ^ 204))]
#guard ((encodeField (.scalar curve) 0).toOption.getD [])[1]! == 2 ^ 48
#guard (encodeField (.scalar curve) (2 ^ 200 + 1)).toOption == some [2 ^ 200, 0]
#guard (encodeField (.scalar curve) (2 ^ 200 + 1) >>= decodeField (.scalar curve)).toOption ==
  some (2 ^ 200 + 1)
#guard rejected (encodeField (.base curve) p) && rejected (encodeField (.scalar curve) l)
#guard rejected (decodeField (.scalar curve) [2 ^ 204, 0])
#guard rejected (decodeField (.scalar curve) [0, 2 ^ 48 + 1])
#guard pointValid curve .identity
#guard pointValid curve generator
#guard !pointValid curve (.affine 0 1)
#guard !pointValid curve (.affine 0 (p - 1))
#guard !pointValid curve generatorPlusOrderTwo
#guard normalizePoint curve 0 1 == .identity
#guard normalizePoint curve 1 1 == .affine 1 1
#guard identityEncoding curve ==
  [(p - 1) % lowRadix, (p - 1) / lowRadix, 0, 0]
#guard (encodePoint curve .identity).toOption == some (identityEncoding curve)
#guard (decodePoint curve (identityEncoding curve)).toOption == some .identity
#guard rejected (decodePoint curve [lowRadix, 0, 0, 0])
#guard rejected (decodePoint curve [0, highRadix, 0, 0])
#guard rejected (decodeField (.base curve) [p % lowRadix, p / lowRadix])
#guard rejected (decodePoint curve [p % lowRadix, p / lowRadix, 0, 0])
#guard rejected (encodePoint curve (.affine p 1))
#guard (encodePoint curve generator >>= decodePoint curve).toOption == some generator
#guard [Curve.secp256k1, .secp256r1].all fun secp =>
  (identityEncoding secp).length == 5 &&
    (decodePoint secp (identityEncoding secp)).toOption == some .identity

def main : IO Unit := do
  let mut fields : Array Lean.Json := #[]
  for kind in [Kind.base curve, .scalar curve] do
    let some modulus := kind.modulus? | throw (IO.userError "missing Curve25519 field modulus")
    let values := if kind == .scalar curve then [0, 1, 2 ^ 200 + 1, modulus - 1]
      else [0, 1, modulus - 1]
    for value in values do
      let encoding ← match encodeField kind value with
        | .ok encoding => pure encoding
        | .error message => throw (IO.userError message)
      fields := fields.push <| Lean.Json.mkObj [
        ("type", Lean.toJson kind.nativeName), ("modulus", Lean.toJson (toString modulus)),
        ("value", Lean.toJson (toString value)),
        ("encoding", Lean.toJson (encoding.map toString))]
  let identity := Lean.Json.mkObj [
    ("type", Lean.toJson (Kind.point curve).nativeName),
    ("encoding", Lean.toJson ((identityEncoding curve).map toString))]
  let encodedGenerator ← match encodePoint curve generator with
    | .ok encoding => pure encoding
    | .error message => throw (IO.userError message)
  let point := Lean.Json.mkObj [
    ("type", Lean.toJson (Kind.point curve).nativeName),
    ("x", Lean.toJson (toString (match generator with | .affine x _ => x | _ => 0))),
    ("y", Lean.toJson (toString (match generator with | .affine _ y => y | _ => 0))),
    ("encoding", Lean.toJson (encodedGenerator.map toString))]
  IO.println <| (Lean.Json.mkObj [
    ("schemaVersion", Lean.toJson (1 : Nat)),
    ("fields", Lean.Json.arr fields),
    ("identities", Lean.toJson [identity]),
    ("points", Lean.toJson [point])]).pretty
