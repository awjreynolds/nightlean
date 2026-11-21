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

-- OpenZeppelin Compact Contracts f85f1a23685c6bbedfc8c2589ae3aa128aff7c46
-- EcdhMask.test.ts pins the three ECDH memo outputs below. Its ElGamal.test.ts
-- uses the public padded `elgamal-ek-A` fixture, whose account ID and tagged
-- scalar are separately pinned from Compact Runtime 0.21.0.
noctium_circuit issue70OpenZeppelinVectors where
  let accountKey : Bytes32 := bytes32("elgamal-ek-A")
  let accountHash : Bytes32 := persistentHashVector32([accountKey])
  let encryptionScalarNative : Native := degradeToNative(persistentHashVector32([
    bytes32("ElGamal:secretToScalar"), accountKey]))
  let encryptionKeyScalar : JubjubScalar := jubjubScalarFromNative(encryptionScalarNative)
  let recipientScalar : JubjubScalar := jubjubScalarFromNative(111222333444555)
  let ephemeralScalar : JubjubScalar := jubjubScalarFromNative(424242)
  let recipientPk : JubjubPoint := jubjubMulGenerator(recipientScalar)
  let ephemeralPk : JubjubPoint := jubjubMulGenerator(ephemeralScalar)
  let shared : JubjubPoint := jubjubMul(recipientPk, ephemeralScalar)
  let sharedDigest : Bytes32 := persistentHashPoint(shared)
  let mask : Native := degradeToNative(persistentHashVector32([
    sharedDigest, bytes32("ecdh_mask_golden")]))
  let value : Native := 170141183460469231731687303715884118073
  let encryptedValue : Native := add(value, mask)
  output computedAccountId : Bytes32 := disclose(accountHash)
  output computedEncryptionScalar : Native := disclose(jubjubScalarToNative(encryptionKeyScalar))
  output computedEphemeralX : Native := disclose(jubjubX(ephemeralPk))
  output computedEphemeralY : Native := disclose(jubjubY(ephemeralPk))
  output computedCiphertext : Native := disclose(encryptedValue)
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
  entry referenceVectors uses issue70OpenZeppelinVectors where
    return accountId : Bytes32 := disclose(computedAccountId)
    return encryptionScalar : Native := disclose(computedEncryptionScalar)
    return ephemeralX : Native := disclose(computedEphemeralX)
    return ephemeralY : Native := disclose(computedEphemeralY)
    return ciphertext : Native := disclose(computedCiphertext)
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
