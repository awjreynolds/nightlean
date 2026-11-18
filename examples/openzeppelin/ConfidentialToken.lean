-- SPDX-License-Identifier: MIT
-- Copyright (c) 2025 Zeppelin Group Ltd
-- Adapted from OpenZeppelin Compact Contracts, ConfidentialFungibleToken.
-- Reference: f85f1a23685c6bbedfc8c2589ae3aa128aff7c46.
import Noctium.Frontend

open scoped Noctium

namespace OpenZeppelinPort

noctium_witness freshSeed() : Bytes32
noctium_witness plaintextBalance(c1 : JubjubPoint, c2 : JubjubPoint) : UInt 128

noctium_private_state Wallet where
  cell accountSecret : Bytes32
  cell encryptionSecret : Bytes32
end

noctium_witness_circuit registerAccount where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  public accountId : Bytes32
  public pk : JubjubPoint
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  let derivedAccountId : Bytes32 := persistentHash32(accountSecret)
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  let derivedPk : JubjubPoint := jubjubMulGenerator(encryptionScalar)
  prove eq(accountId, derivedAccountId)
  prove eq(pk, derivedPk)
  prove eq(eq(derivedPk, identity), false)
  output keyX : Native := disclose(jubjubX(derivedPk))
  output keyY : Native := disclose(jubjubY(derivedPk))
end

noctium_witness_circuit creditPending where
  public recipient : Bytes32
  private value : UInt 128
  public recipientPk : JubjubPoint
  public previousC1X : Native
  public previousC1Y : Native
  public previousC2X : Native
  public previousC2Y : Native
  public epoch : UInt 64
  let seed : Bytes32 := witness freshSeed()
  let key : JubjubPoint := recipientPk
  let previousC1 : JubjubPoint := jubjubFromCoordinates(previousC1X, previousC1Y)
  let previousC2 : JubjubPoint := jubjubFromCoordinates(previousC2X, previousC2Y)
  let valueField : Native := cast(Native, value)
  let valuePoint : JubjubPoint := jubjubMulGenerator(jubjubScalarFromNative(valueField))
  let countHash : Bytes32 := persistentHashNative(cast(Native, epoch))
  let balanceR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("credit_balance"), recipient, countHash])))
  let memoR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("credit_memo"), recipient, countHash])))
  prove eq(eq(jubjubScalarToNative(balanceR), 0), false)
  prove eq(eq(jubjubScalarToNative(memoR), 0), false)
  prove eq(eq(recipient, bytes32("")), false)
  let nextC1 : JubjubPoint := jubjubAdd(previousC1, jubjubMulGenerator(balanceR))
  let nextC2 : JubjubPoint := jubjubAdd(
    jubjubAdd(previousC2, valuePoint), jubjubMul(key, balanceR))
  let ephemeral : JubjubPoint := jubjubMulGenerator(memoR)
  let shared : JubjubPoint := jubjubMul(key, memoR)
  let memoDigest : Bytes32 := persistentHashPoint(shared)
  let memoMask : Native := degradeToNative(persistentHashVector32([
    memoDigest, bytes32("OZ_CFT_ecdh_memo_v1")]))
  let memoValue : Native := add(valueField, memoMask)
  output nextC1X : Native := disclose(jubjubX(nextC1))
  output nextC1Y : Native := disclose(jubjubY(nextC1))
  output nextC2X : Native := disclose(jubjubX(nextC2))
  output nextC2Y : Native := disclose(jubjubY(nextC2))
  output memoX : Native := disclose(jubjubX(ephemeral))
  output memoY : Native := disclose(jubjubY(ephemeral))
  output memoAmount : Native := disclose(memoValue)
end

noctium_witness_circuit sweepPending where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  public accountId : Bytes32
  public balanceC1X : Native
  public balanceC1Y : Native
  public balanceC2X : Native
  public balanceC2Y : Native
  public pendingC1X : Native
  public pendingC1Y : Native
  public pendingC2X : Native
  public pendingC2Y : Native
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  let derivedAccountId : Bytes32 := persistentHash32(accountSecret)
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  let derivedPk : JubjubPoint := jubjubMulGenerator(encryptionScalar)
  let balanceC1 : JubjubPoint := jubjubFromCoordinates(balanceC1X, balanceC1Y)
  let balanceC2 : JubjubPoint := jubjubFromCoordinates(balanceC2X, balanceC2Y)
  let pendingC1 : JubjubPoint := jubjubFromCoordinates(pendingC1X, pendingC1Y)
  let pendingC2 : JubjubPoint := jubjubFromCoordinates(pendingC2X, pendingC2Y)
  let nextC1 : JubjubPoint := jubjubAdd(balanceC1, pendingC1)
  let nextC2 : JubjubPoint := jubjubAdd(balanceC2, pendingC2)
  prove eq(accountId, derivedAccountId)
  prove eq(eq(derivedPk, identity), false)
  output keyX : Native := disclose(jubjubX(derivedPk))
  output keyY : Native := disclose(jubjubY(derivedPk))
  output nextC1X : Native := disclose(jubjubX(nextC1))
  output nextC1Y : Native := disclose(jubjubY(nextC1))
  output nextC2X : Native := disclose(jubjubX(nextC2))
  output nextC2Y : Native := disclose(jubjubY(nextC2))
end

noctium_witness_circuit transferValue where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  public accountId : Bytes32
  public recipient : Bytes32
  private value : UInt 128
  public recipientPk : JubjubPoint
  public balanceC1X : Native
  public balanceC1Y : Native
  public balanceC2X : Native
  public balanceC2Y : Native
  public pendingC1X : Native
  public pendingC1Y : Native
  public pendingC2X : Native
  public pendingC2Y : Native
  public epoch : UInt 64
  let seed : Bytes32 := witness freshSeed()
  let plaintext : UInt 128 := witness plaintextBalance(
    jubjubFromCoordinates(balanceC1X, balanceC1Y),
    jubjubFromCoordinates(balanceC2X, balanceC2Y))
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  let derivedAccountId : Bytes32 := persistentHash32(accountSecret)
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  let ownerPk : JubjubPoint := jubjubMulGenerator(encryptionScalar)
  let ownerC1 : JubjubPoint := jubjubFromCoordinates(balanceC1X, balanceC1Y)
  let ownerC2 : JubjubPoint := jubjubFromCoordinates(balanceC2X, balanceC2Y)
  let recipientC1 : JubjubPoint := jubjubFromCoordinates(pendingC1X, pendingC1Y)
  let recipientC2 : JubjubPoint := jubjubFromCoordinates(pendingC2X, pendingC2Y)
  let valueField : Native := cast(Native, value)
  let remaining : UInt 128 := sub(plaintext, value)
  let valuePoint : JubjubPoint := jubjubMulGenerator(jubjubScalarFromNative(valueField))
  let debitHash : Bytes32 := persistentHashVector32([
    seed, bytes32("debit_balance")])
  let debitR : JubjubScalar := jubjubScalarFromNative(degradeToNative(debitHash))
  prove eq(eq(jubjubScalarToNative(debitR), 0), false)
  let nextOwnerC1 : JubjubPoint := jubjubAdd(ownerC1, jubjubNeg(jubjubMulGenerator(debitR)))
  let nextOwnerC2 : JubjubPoint := jubjubAdd(ownerC2,
    jubjubNeg(jubjubAdd(valuePoint, jubjubMul(ownerPk, debitR))))
  let recovered : JubjubPoint := jubjubAdd(nextOwnerC2,
    jubjubNeg(jubjubMul(nextOwnerC1, encryptionScalar)))
  let remainingPoint : JubjubPoint := jubjubMulGenerator(
    jubjubScalarFromNative(cast(Native, remaining)))
  let countHash : Bytes32 := persistentHashNative(cast(Native, epoch))
  let creditR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("credit_balance"), recipient, countHash])))
  prove eq(eq(jubjubScalarToNative(creditR), 0), false)
  let nextRecipientC1 : JubjubPoint := jubjubAdd(
    recipientC1, jubjubMulGenerator(creditR))
  let nextRecipientC2 : JubjubPoint := jubjubAdd(
    jubjubAdd(recipientC2, valuePoint), jubjubMul(recipientPk, creditR))
  let memoR : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([seed, bytes32("credit_memo"), recipient, countHash])))
  prove eq(eq(jubjubScalarToNative(memoR), 0), false)
  let ephemeral : JubjubPoint := jubjubMulGenerator(memoR)
  let shared : JubjubPoint := jubjubMul(recipientPk, memoR)
  let memoDigest : Bytes32 := persistentHashPoint(shared)
  let memoMask : Native := degradeToNative(persistentHashVector32([
    memoDigest, bytes32("OZ_CFT_ecdh_memo_v1")]))
  let memoValue : Native := add(valueField, memoMask)
  prove eq(accountId, derivedAccountId)
  prove eq(eq(ownerPk, identity), false)
  prove eq(eq(recipientPk, identity), false)
  prove eq(eq(accountId, recipient), false)
  prove eq(jubjubAdd(ownerC2,
    jubjubNeg(jubjubMul(ownerC1, encryptionScalar))),
    jubjubMulGenerator(jubjubScalarFromNative(cast(Native, plaintext))))
  prove eq(recovered, remainingPoint)
  prove eq(eq(recipient, bytes32("")), false)
  output ownerKeyX : Native := disclose(jubjubX(ownerPk))
  output ownerKeyY : Native := disclose(jubjubY(ownerPk))
  output nextOwnerC1X : Native := disclose(jubjubX(nextOwnerC1))
  output nextOwnerC1Y : Native := disclose(jubjubY(nextOwnerC1))
  output nextOwnerC2X : Native := disclose(jubjubX(nextOwnerC2))
  output nextOwnerC2Y : Native := disclose(jubjubY(nextOwnerC2))
  output nextRecipientC1X : Native := disclose(jubjubX(nextRecipientC1))
  output nextRecipientC1Y : Native := disclose(jubjubY(nextRecipientC1))
  output nextRecipientC2X : Native := disclose(jubjubX(nextRecipientC2))
  output nextRecipientC2Y : Native := disclose(jubjubY(nextRecipientC2))
  output memoX : Native := disclose(jubjubX(ephemeral))
  output memoY : Native := disclose(jubjubY(ephemeral))
  output memoAmount : Native := disclose(memoValue)
end

noctium_witness_circuit debitBalance where
  read private Wallet.accountSecret as accountSecret
  read private Wallet.encryptionSecret as encryptionSecret
  public accountId : Bytes32
  private value : UInt 128
  public balanceC1X : Native
  public balanceC1Y : Native
  public balanceC2X : Native
  public balanceC2Y : Native
  let seed : Bytes32 := witness freshSeed()
  let plaintext : UInt 128 := witness plaintextBalance(
    jubjubFromCoordinates(balanceC1X, balanceC1Y),
    jubjubFromCoordinates(balanceC2X, balanceC2Y))
  let identity : JubjubPoint := jubjubFromCoordinates(0, 1)
  let derivedAccountId : Bytes32 := persistentHash32(accountSecret)
  let encryptionScalar : JubjubScalar := jubjubScalarFromNative(degradeToNative(
    persistentHashVector32([bytes32("ElGamal:secretToScalar"), encryptionSecret])))
  let ownerPk : JubjubPoint := jubjubMulGenerator(encryptionScalar)
  let ownerC1 : JubjubPoint := jubjubFromCoordinates(balanceC1X, balanceC1Y)
  let ownerC2 : JubjubPoint := jubjubFromCoordinates(balanceC2X, balanceC2Y)
  let remaining : UInt 128 := sub(plaintext, value)
  let valueField : Native := cast(Native, value)
  let valuePoint : JubjubPoint := jubjubMulGenerator(jubjubScalarFromNative(valueField))
  let debitHash : Bytes32 := persistentHashVector32([
    seed, bytes32("debit_balance")])
  let debitR : JubjubScalar := jubjubScalarFromNative(degradeToNative(debitHash))
  let nextC1 : JubjubPoint := jubjubAdd(ownerC1, jubjubNeg(jubjubMulGenerator(debitR)))
  let nextC2 : JubjubPoint := jubjubAdd(ownerC2,
    jubjubNeg(jubjubAdd(valuePoint, jubjubMul(ownerPk, debitR))))
  let recovered : JubjubPoint := jubjubAdd(nextC2,
    jubjubNeg(jubjubMul(nextC1, encryptionScalar)))
  let remainingPoint : JubjubPoint := jubjubMulGenerator(
    jubjubScalarFromNative(cast(Native, remaining)))
  prove eq(accountId, derivedAccountId)
  prove eq(eq(ownerPk, identity), false)
  prove eq(eq(jubjubScalarToNative(debitR), 0), false)
  prove eq(jubjubAdd(ownerC2,
    jubjubNeg(jubjubMul(ownerC1, encryptionScalar))),
    jubjubMulGenerator(jubjubScalarFromNative(cast(Native, plaintext))))
  prove eq(recovered, remainingPoint)
  output keyX : Native := disclose(jubjubX(ownerPk))
  output keyY : Native := disclose(jubjubY(ownerPk))
  output nextC1X : Native := disclose(jubjubX(nextC1))
  output nextC1Y : Native := disclose(jubjubY(nextC1))
  output nextC2X : Native := disclose(jubjubX(nextC2))
  output nextC2Y : Native := disclose(jubjubY(nextC2))
end

noctium_circuit accountView where
  public account : Bytes32
end

noctium_circuit noViewInputs where
end

noctium_circuit accountSecretInput where
  private secret : Bytes32
end

noctium_contract ConfidentialToken where
  tree encryptionKeys : Bytes32 => struct JubjubKey {
    x : Native
    y : Native
  }
  tree balances : Bytes32 => struct SpendableCiphertext {
    c1x : Native
    c1y : Native
    c2x : Native
    c2y : Native
  }
  tree pending : Bytes32 => struct PendingCiphertext {
    c1x : Native
    c1y : Native
    c2x : Native
    c2y : Native
  }
  tree memos : Bytes32 => List struct Memo {
    ephemeralX : Native
    ephemeralY : Native
    amount : Native
  }
  tree creditEpochs : Bytes32 => Counter
  cell initialized : Bool
  cell totalSupply : UInt 128

  entry registerWithKey uses registerAccount where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(accountId)] as alreadyRegistered
    require eq(alreadyRegistered, false)
    insert encryptionKeys[disclose(accountId)] := fields(result.keyX, result.keyY)
    insert balances[disclose(accountId)] := fields(0, 1, 0, 1)
    insert pending[disclose(accountId)] := fields(0, 1, 0, 1)
    return caller : Bytes32 := accountId
  end

  entry mint uses creditPending where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(recipient)] as registered
    require eq(registered, true)
    read encryptionKeys[disclose(recipient)] as recipientKey
    require eq(recipientKey_x, jubjubX(recipientPk))
    require eq(recipientKey_y, jubjubY(recipientPk))
    read pending[disclose(recipient)] as previousPending
    require eq(previousPending_c1x, previousC1X)
    require eq(previousPending_c1y, previousC1Y)
    require eq(previousPending_c2x, previousC2X)
    require eq(previousPending_c2y, previousC2Y)
    member memos[disclose(recipient)] as memoListPresent
    if eq(memoListPresent, false) then {
      reset memos[disclose(recipient)]
    } else {
    }
    member creditEpochs[disclose(recipient)] as epochPresent
    if eq(epochPresent, false) then {
      reset creditEpochs[disclose(recipient)]
    } else {
    }
    increment creditEpochs[disclose(recipient)] by 1
    read creditEpochs[disclose(recipient)] as actualEpoch
    require eq(actualEpoch, epoch)
    pushFront memos[disclose(recipient)] := fields(
      result.memoX, result.memoY, result.memoAmount)
    write pending[disclose(recipient)] := fields(
      result.nextC1X, result.nextC1Y, result.nextC2X, result.nextC2Y)
    read totalSupply as oldSupply
    write totalSupply := disclose(cast(UInt 128, add(oldSupply, value)))
  end

  entry sweep uses sweepPending where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(accountId)] as registered
    require eq(registered, true)
    read encryptionKeys[disclose(accountId)] as storedKey
    require eq(storedKey_x, result.keyX)
    require eq(storedKey_y, result.keyY)
    read balances[disclose(accountId)] as oldBalance
    require eq(oldBalance_c1x, balanceC1X)
    require eq(oldBalance_c1y, balanceC1Y)
    require eq(oldBalance_c2x, balanceC2X)
    require eq(oldBalance_c2y, balanceC2Y)
    read pending[disclose(accountId)] as oldPending
    require eq(oldPending_c1x, pendingC1X)
    require eq(oldPending_c1y, pendingC1Y)
    require eq(oldPending_c2x, pendingC2X)
    require eq(oldPending_c2y, pendingC2Y)
    write balances[disclose(accountId)] := fields(
      result.nextC1X, result.nextC1Y, result.nextC2X, result.nextC2Y)
    write pending[disclose(accountId)] := fields(0, 1, 0, 1)
    return caller : Bytes32 := accountId
  end

  entry transfer uses transferValue where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(accountId)] as senderRegistered
    require eq(senderRegistered, true)
    member encryptionKeys[disclose(recipient)] as recipientRegistered
    require eq(recipientRegistered, true)
    require eq(eq(accountId, recipient), false)
    read encryptionKeys[disclose(accountId)] as senderKey
    require eq(senderKey_x, result.ownerKeyX)
    require eq(senderKey_y, result.ownerKeyY)
    read encryptionKeys[disclose(recipient)] as recipientKey
    require eq(recipientKey_x, jubjubX(recipientPk))
    require eq(recipientKey_y, jubjubY(recipientPk))
    read balances[disclose(accountId)] as oldBalance
    require eq(oldBalance_c1x, balanceC1X)
    require eq(oldBalance_c1y, balanceC1Y)
    require eq(oldBalance_c2x, balanceC2X)
    require eq(oldBalance_c2y, balanceC2Y)
    read pending[disclose(recipient)] as oldPending
    require eq(oldPending_c1x, pendingC1X)
    require eq(oldPending_c1y, pendingC1Y)
    require eq(oldPending_c2x, pendingC2X)
    require eq(oldPending_c2y, pendingC2Y)
    member memos[disclose(recipient)] as memoListPresent
    if eq(memoListPresent, false) then {
      reset memos[disclose(recipient)]
    } else {
    }
    member creditEpochs[disclose(recipient)] as epochPresent
    if eq(epochPresent, false) then {
      reset creditEpochs[disclose(recipient)]
    } else {
    }
    increment creditEpochs[disclose(recipient)] by 1
    read creditEpochs[disclose(recipient)] as actualEpoch
    require eq(actualEpoch, epoch)
    write balances[disclose(accountId)] := fields(
      result.nextOwnerC1X, result.nextOwnerC1Y,
      result.nextOwnerC2X, result.nextOwnerC2Y)
    write pending[disclose(recipient)] := fields(
      result.nextRecipientC1X, result.nextRecipientC1Y,
      result.nextRecipientC2X, result.nextRecipientC2Y)
    pushFront memos[disclose(recipient)] := fields(
      result.memoX, result.memoY, result.memoAmount)
    return caller : Bytes32 := accountId
  end

  entry burn uses debitBalance where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member encryptionKeys[disclose(accountId)] as registered
    require eq(registered, true)
    read encryptionKeys[disclose(accountId)] as senderKey
    require eq(senderKey_x, result.keyX)
    require eq(senderKey_y, result.keyY)
    read balances[disclose(accountId)] as oldBalance
    require eq(oldBalance_c1x, balanceC1X)
    require eq(oldBalance_c1y, balanceC1Y)
    require eq(oldBalance_c2x, balanceC2X)
    require eq(oldBalance_c2y, balanceC2Y)
    read totalSupply as oldSupply
    write balances[disclose(accountId)] := fields(
      result.nextC1X, result.nextC1Y, result.nextC2X, result.nextC2Y)
    write totalSupply := disclose(sub(oldSupply, value))
    return caller : Bytes32 := accountId
  end

  entry totalSupply uses noViewInputs where
    read totalSupply as currentSupply
    return supply : UInt 128 := currentSupply
  end

  entry isRegistered uses accountView where
    member encryptionKeys[disclose(account)] as registered
    return value : Bool := registered
  end

  entry balanceOf uses accountView where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member balances[disclose(account)] as balancePresent
    when eq(balancePresent, true) read balances[disclose(account)] as currentBalance
    return c1 : JubjubPoint := jubjubFromCoordinates(
      select(balancePresent, currentBalance_c1x, 0),
      select(balancePresent, currentBalance_c1y, 1))
    return c2 : JubjubPoint := jubjubFromCoordinates(
      select(balancePresent, currentBalance_c2x, 0),
      select(balancePresent, currentBalance_c2y, 1))
  end

  entry pendingOf uses accountView where
    read initialized as isInitialized
    require eq(isInitialized, true)
    member pending[disclose(account)] as pendingPresent
    when eq(pendingPresent, true) read pending[disclose(account)] as currentPending
    return c1 : JubjubPoint := jubjubFromCoordinates(
      select(pendingPresent, currentPending_c1x, 0),
      select(pendingPresent, currentPending_c1y, 1))
    return c2 : JubjubPoint := jubjubFromCoordinates(
      select(pendingPresent, currentPending_c2x, 0),
      select(pendingPresent, currentPending_c2y, 1))
  end

  entry computeAccountId uses accountSecretInput where
    return accountId : Bytes32 := disclose(persistentHash32(secret))
  end
end

end OpenZeppelinPort
