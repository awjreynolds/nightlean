import Noctium.Frontend

open scoped Noctium

noctium_circuit unshieldedMintRecipientInputs where
  public domain : Bytes32
  public amount : UInt 64
  public isContract : Bool
  public recipient : Bytes32
end

noctium_contract NativeUnshieldedMintRecipient where
  entry mint uses unshieldedMintRecipientInputs where
    readSelf as own
    mintUnshielded(domain, amount)
    claimUnshieldedCoinSpend(persistentHashVector32([
      bytes32("midnight:derive_token"), domain, own]),
      cast(UInt 128, amount), true, isContract, recipient)
    when boolAnd(isContract, eq(recipient, own))
      incUnshieldedInputs(persistentHashVector32([
        bytes32("midnight:derive_token"), domain, own]), cast(UInt 128, amount), true)
    return color : Bytes32 := disclose(persistentHashVector32([
      bytes32("midnight:derive_token"), domain, own]))
  end
end
