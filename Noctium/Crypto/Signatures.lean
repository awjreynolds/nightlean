import Noctium.IR

namespace Noctium.Crypto

private def ecdsaVerify (curve : Foreign.Curve) (msgHash : Expr (.bytes 32))
    (r s : Expr (.foreign (.scalar curve)))
    (pk : Expr (.foreign (.point curve))) : Expr .bool := Id.run do
  let z : Expr (.foreign (.scalar curve)) :=
    .foreignFromBytes (.scalar curve) (.reverseBytes32 msgHash)
  let w : Expr (.foreign (.scalar curve)) := .foreignUnary (.inv (.scalar curve)) s
  let u1 : Expr (.foreign (.scalar curve)) := .foreignBinary (.mul (.scalar curve)) z w
  let u2 : Expr (.foreign (.scalar curve)) := .foreignBinary (.mul (.scalar curve)) r w
  let generatorTerm : Expr (.foreign (.point curve)) :=
    .foreignUnary (.mulGenerator curve) u1
  let publicKeyTerm : Expr (.foreign (.point curve)) := .foreignBinary (.ecMul curve) pk u2
  let point : Expr (.foreign (.point curve)) :=
    .foreignBinary (.add (.point curve)) generatorTerm publicKeyTerm
  let x : Expr (.foreign (.base curve)) := .foreignUnary (.x curve) point
  let xModN : Expr (.foreign (.scalar curve)) := .foreignFromBytes (.scalar curve) (.foreignToBytes x)
  let nonIdentity := .eq (.eq pk (.foreignIdentity curve)) (.bool false)
  let nonzeroR := .eq (.eq r (.foreignScalar curve 0)) (.bool false)
  let nonzeroS := .eq (.eq s (.foreignScalar curve 0)) (.bool false)
  return .assertE nonIdentity (.assertE nonzeroR (.assertE nonzeroS (.eq xModN r)))

def secp256k1EcdsaVerify (msgHash : Expr (.bytes 32))
    (r s : Expr (.foreign (.scalar .secp256k1)))
    (pk : Expr (.foreign (.point .secp256k1))) : Expr .bool :=
  ecdsaVerify .secp256k1 msgHash r s pk

def secp256r1EcdsaVerify (msgHash : Expr (.bytes 32))
    (r s : Expr (.foreign (.scalar .secp256r1)))
    (pk : Expr (.foreign (.point .secp256r1))) : Expr .bool :=
  ecdsaVerify .secp256r1 msgHash r s pk

def jubjubSchnorrVerify (msg : List (Expr .native))
    (announcement : Expr .jubjubPoint) (response : Expr .native)
    (pk : Expr .jubjubPoint) : Expr .bool := Id.run do
  let challengeInputs : List (Expr .native) :=
    [Expr.jubjubCoordinate announcement 0, Expr.jubjubCoordinate announcement 1,
      Expr.jubjubCoordinate pk 0, Expr.jubjubCoordinate pk 1] ++ msg
  let challenge := Expr.jubjubScalarFromNative (.transientHash challengeInputs)
  let lhs := Expr.jubjubMulGenerator (Expr.jubjubScalarFromNative response)
  let rhs := Expr.jubjubAdd announcement (Expr.jubjubMul pk challenge)
  let identity := Expr.jubjubFromCoordinates (.native 0) (.native 1)
  let nonIdentity := Expr.eq (.eq pk identity) (.bool false)
  return .assertE nonIdentity (.eq lhs rhs)

def ed25519Verify {length : Nat} (msg : Expr (.bytes length))
    (r : Expr (.foreign (.point .curve25519)))
    (s : Expr (.foreign (.scalar .curve25519)))
    (pk : Expr (.foreign (.point .curve25519))) : Expr .bool := Id.run do
  let encodedR : Expr (.bytes 32) := .foreignToBytes r
  let encodedPk : Expr (.bytes 32) := .foreignToBytes pk
  let preimage := Expr.concatBytes (Expr.concatBytes encodedR encodedPk) msg
  let challengeBytes := Expr.sha512 preimage
  let challenge : Expr (.foreign (.scalar .curve25519)) :=
    .foreignFromBytes (.scalar .curve25519) challengeBytes
  let lhs : Expr (.foreign (.point .curve25519)) :=
    .foreignUnary (.mulGenerator .curve25519) s
  let publicKeyTerm : Expr (.foreign (.point .curve25519)) :=
    .foreignBinary (.ecMul .curve25519) pk challenge
  let rhs : Expr (.foreign (.point .curve25519)) :=
    .foreignBinary (.add (.point .curve25519)) r publicKeyTerm
  let x : Expr (.foreign (.base .curve25519)) := .foreignUnary (.x .curve25519) pk
  let nonIdentity := .eq (.eq x (.foreignBase .curve25519 0)) (.bool false)
  return .assertE nonIdentity (.eq lhs rhs)

def secp256k1EthereumAddress (pk : Expr (.foreign (.point .secp256k1))) : Expr (.bytes 20) :=
  let x : Expr (.foreign (.base .secp256k1)) := .foreignUnary (.x .secp256k1) pk
  let y : Expr (.foreign (.base .secp256k1)) := .foreignUnary (.y .secp256k1) pk
  let coordinates := Expr.concatBytes (Expr.reverseBytes (.foreignToBytes x))
    (Expr.reverseBytes (.foreignToBytes y))
  let address := Expr.sliceBytes (.keccak256 coordinates) 12 32
  let nonIdentity := Expr.eq (Expr.eq pk (.foreignIdentity .secp256k1)) (.bool false)
  Expr.assertE nonIdentity address

end Noctium.Crypto
