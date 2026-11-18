import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium

-- Deterministic fixture domains. Applications must keep invocation seeds fresh and secret.
noctium_circuit issue70DerivedCrypto where
  private accountSecret : Bytes32
  private encryptionSecret : Bytes32
  private seed : Bytes32
  private amount : UInt 128
  public account : Bytes32
  public pk : JubjubPoint
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  assert eq(account, persistentHash32(accountSecret))
  let keyScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  assert eq(pk, jubjubMulGenerator(keyScalar))
  assert eq(eq(pk, identity), false)
  let balanceR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("Noctium:balance")])) )
  let memoR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("Noctium:memo")])) )
  assert eq(eq(jubjubScalarToNative(balanceR), 0), false)
  assert eq(eq(jubjubScalarToNative(memoR), 0), false)
  let value : Native := cast(Native, amount)
  let valuePoint : JubjubPoint := jubjubMulGenerator(jubjubScalarFromNative(value))
  let c1 : JubjubPoint := jubjubMulGenerator(balanceR)
  let c2 : JubjubPoint := jubjubAdd(valuePoint, jubjubMul(pk, balanceR))
  assert eq(jubjubAdd(c2, jubjubNeg(jubjubMul(c1, keyScalar))), valuePoint)
  let ephemeral : JubjubPoint := jubjubMulGenerator(memoR)
  let shared : JubjubPoint := jubjubMul(pk, memoR)
  let recoveredShared : JubjubPoint := jubjubMul(ephemeral, keyScalar)
  let digest : Bytes32 := persistentHashPoint(shared)
  let recoveredDigest : Bytes32 := persistentHashPoint(recoveredShared)
  let mask : Native := degradeToNative(persistentHashVector32([
    digest, bytes32("Noctium:memo:amount")]))
  let recoveredMask : Native := degradeToNative(persistentHashVector32([
    recoveredDigest, bytes32("Noctium:memo:amount")]))
  let memoValue : Native := add(value, mask)
  assert eq(sub(memoValue, recoveredMask), value)
  output c1x : Native := disclose(jubjubX(c1))
  output c1y : Native := disclose(jubjubY(c1))
  output c2x : Native := disclose(jubjubX(c2))
  output c2y : Native := disclose(jubjubY(c2))
  output ex : Native := disclose(jubjubX(ephemeral))
  output ey : Native := disclose(jubjubY(ephemeral))
  output memo : Native := disclose(memoValue)
end

noctium_contract Issue70DerivedCrypto where
  tree records : Bytes32 => struct EncryptedRecord {
    c1x : Native
    c1y : Native
    c2x : Native
    c2y : Native
    ex : Native
    ey : Native
    memo : Native
  }
  entry encrypt uses issue70DerivedCrypto where
    write records[account] := fields(c1x, c1y, c2x, c2y, ex, ey, memo)
  end
end

#guard match Noctium.Disclosure.circuit {
    name := "unreleasedPointDigest"
    inputs := [{name := "point", ty := .jubjubPoint, visibility := .private}]
    outputs := [{name := "digest", ty := .bytes 32, value := .persistentHashNativeVector [
      .jubjubCoordinate (.ref "point") 0, .jubjubCoordinate (.ref "point") 1]}]
  } with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
