import Noctium.Frontend

open scoped Noctium

noctium_witness randomnessSeed() : Bytes32
noctium_witness plaintext() : UInt 128

noctium_private_state Wallet where
  cell accountSecret : Bytes32
  cell encryptionSecret : Bytes32
  cell lastSeed : Bytes32
end

noctium_witness_circuit register where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  let seed : Bytes32 := witness randomnessSeed()
  let plaintextField : UInt 128 := witness plaintext()
  public account : Bytes32
  public recipient : JubjubPoint
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  prove eq(account, persistentHash32(accountSecret))
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  prove eq(recipient, jubjubMulGenerator(encryptionScalar))
  prove eq(eq(recipient, identity), false)
  let balanceR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("Noctium:balance")])))
  let memoR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("Noctium:memo")])))
  prove eq(eq(jubjubScalarToNative(encryptionScalar), 0), false)
  prove eq(eq(jubjubScalarToNative(balanceR), 0), false)
  prove eq(eq(jubjubScalarToNative(memoR), 0), false)
  let amount : Native := cast(Native, plaintextField)
  let amountPoint : JubjubPoint := jubjubMulGenerator(jubjubScalarFromNative(amount))
  let c1 : JubjubPoint := jubjubMulGenerator(balanceR)
  let c2 : JubjubPoint := jubjubAdd(amountPoint, jubjubMul(recipient, balanceR))
  prove eq(jubjubAdd(c2, jubjubNeg(jubjubMul(c1, encryptionScalar))), amountPoint)
  let ephemeral : JubjubPoint := jubjubMulGenerator(memoR)
  let shared : JubjubPoint := jubjubMul(recipient, memoR)
  let recoveredShared : JubjubPoint := jubjubMul(ephemeral, encryptionScalar)
  let memoDigest : Bytes32 := persistentHashPoint(shared)
  let recoveredDigest : Bytes32 := persistentHashPoint(recoveredShared)
  let memoMask : Native := degradeToNative(persistentHashVector32([
    memoDigest, bytes32("Noctium:memo:amount")]))
  let recoveredMask : Native := degradeToNative(persistentHashVector32([
    recoveredDigest, bytes32("Noctium:memo:amount")]))
  let memoCiphertext : Native := add(amount, memoMask)
  prove eq(sub(memoCiphertext, recoveredMask), amount)
  stage Wallet.lastSeed := seed
  output c1x : Native := disclose(jubjubX(c1))
  output c1y : Native := disclose(jubjubY(c1))
  output c2x : Native := disclose(jubjubX(c2))
  output c2y : Native := disclose(jubjubY(c2))
  output memoX : Native := disclose(jubjubX(ephemeral))
  output memoY : Native := disclose(jubjubY(ephemeral))
  output memoAmount : Native := disclose(memoCiphertext)
end

noctium_contract HashWitness where
  cell c1x : Native
  cell c1y : Native
  cell c2x : Native
  cell c2y : Native
  cell memoX : Native
  cell memoY : Native
  cell memoAmount : Native
  entry register uses register where
    write c1x := result.c1x
    write c1y := result.c1y
    write c2x := result.c2x
    write c2y := result.c2y
    write memoX := result.memoX
    write memoY := result.memoY
    write memoAmount := result.memoAmount
  end
end
