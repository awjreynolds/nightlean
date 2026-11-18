import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit signatureChecksValues where
  private kDigest : Bytes 32
  private kR : Secp256k1Scalar
  private kS : Secp256k1Scalar
  private kKey : Secp256k1Point
  private pDigest : Bytes 32
  private pR : Secp256r1Scalar
  private pS : Secp256r1Scalar
  private pKey : Secp256r1Point
  private jMessage0 : Native
  private jMessage1 : Native
  private jAnnouncement : JubjubPoint
  private jResponse : Native
  private jKey : JubjubPoint
  private edEmpty : Bytes 0
  private edChanged : Bytes 1
  private edR : Curve25519Point
  private edS : Curve25519Scalar
  private edKey : Curve25519Point
  private ethKey : Secp256k1Point
  output kValid : Bool := disclose(secp256k1EcdsaVerify(kDigest, kR, kS, kKey))
  output pValid : Bool := disclose(secp256r1EcdsaVerify(pDigest, pR, pS, pKey))
  output jValid : Bool := disclose(jubjubSchnorrVerify([jMessage0, jMessage1], jAnnouncement, jResponse, jKey))
  output edValid : Bool := disclose(ed25519Verify(edEmpty, edR, edS, edKey))
  output edChangedValid : Bool := disclose(ed25519Verify(edChanged, edR, edS, edKey))
  output address : Bytes 20 := disclose(secp256k1EthereumAddress(ethKey))
end

noctium_contract SignatureChecks where
  entry verify uses signatureChecksValues where
    return secp256k1Valid : Bool := kValid
    return p256Valid : Bool := pValid
    return schnorrValid : Bool := jValid
    return ed25519Valid : Bool := edValid
    return changedEd25519Valid : Bool := edChangedValid
    return ethereumAddress : Bytes 20 := address
  end
end

#guard match SignatureChecks.validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Disclosure.circuit signatureChecksValues with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Disclosure.circuit {
  name := "undisclosedSignatureResult"
  inputs := [{name := "key", ty := .foreign (.point .secp256k1), visibility := .private}]
  outputs := [{name := "valid", ty := .bool, value := (Crypto.secp256k1EcdsaVerify
    (.bytes32Literal (List.replicate 32 0)) (.foreignScalar .secp256k1 1)
    (.foreignScalar .secp256k1 1) (.ref "key"))}]
} with
  | .error _ => Bool.true
  | .ok _ => Bool.false

/-- error: Noctium expression type mismatch -/
#guard_msgs in
noctium_circuit mismatchedSignatureCurve where
  private digest : Bytes 32
  private r : Secp256r1Scalar
  private s : Secp256k1Scalar
  private key : Secp256k1Point
  output valid : Bool := disclose(secp256k1EcdsaVerify(digest, r, s, key))
end

/-- error: ed25519Verify input exceeds 1024 bytes -/
#guard_msgs in
noctium_circuit oversizedEd25519Message where
  private message : Bytes 961
  private r : Curve25519Point
  private s : Curve25519Scalar
  private key : Curve25519Point
  output valid : Bool := disclose(ed25519Verify(message, r, s, key))
end
