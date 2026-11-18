import Noctium.Foreign
import Lean

open Noctium.Foreign

private def fieldKinds : List Kind :=
  [.base .secp256k1, .scalar .secp256k1, .base .secp256r1, .scalar .secp256r1]

private def rejected (value : Except String α) : Bool := !value.isOk

#guard fieldKinds.all fun kind => (encodeField kind 1).toOption == some [0, 0]
#guard fieldKinds.all fun kind => match kind.modulus? with
  | none => false
  | some modulus => [0, 1, modulus - 1].all fun value =>
      (encodeField kind value >>= decodeField kind).toOption == some value
#guard fieldKinds.all fun kind => match kind.modulus? with
  | none => false
  | some modulus => rejected (encodeField kind modulus) &&
      rejected (decodeField kind [modulus % lowRadix, modulus / lowRadix])
#guard fieldKinds.all fun kind =>
  rejected (decodeField kind [lowRadix, 0]) &&
  rejected (decodeField kind [0, highRadix]) &&
  rejected (decodeField kind [0]) && rejected (decodeField kind [0, 0, 0])
#guard rejected (encodeField (.point .secp256k1) 0)
#guard rejected (decodeField (.point .secp256r1) [0, 0])
#guard [Curve.secp256k1, .secp256r1].all fun curve =>
  identityEncoding curve != [0, 0, 0, 0, 1] &&
    (identityEncoding curve).length == (Kind.point curve).encodedFieldCount
#guard lowRadix < Noctium.Field.modulus && highRadix < Noctium.Field.modulus

def main : IO Unit := do
  let mut fields : Array Lean.Json := #[]
  for kind in fieldKinds do
    let some modulus := kind.modulus? | throw (IO.userError "missing foreign field modulus")
    for value in [0, 1, modulus - 1] do
      let encoding ← match encodeField kind value with
        | .ok encoding => pure encoding
        | .error message => throw (IO.userError message)
      fields := fields.push <| Lean.Json.mkObj [
        ("type", Lean.toJson kind.nativeName), ("modulus", Lean.toJson (toString modulus)),
        ("value", Lean.toJson (toString value)),
        ("encoding", Lean.toJson (encoding.map toString))]
  let identities := [Curve.secp256k1, .secp256r1].map fun curve =>
    Lean.Json.mkObj [
      ("type", Lean.toJson (Kind.point curve).nativeName),
      ("encoding", Lean.toJson ((identityEncoding curve).map toString))]
  IO.println <| (Lean.Json.mkObj [
    ("schemaVersion", Lean.toJson (1 : Nat)),
    ("fields", Lean.Json.arr fields), ("identities", Lean.toJson identities)]).pretty
