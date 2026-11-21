import Noctium.Frontend

open scoped Noctium

noctium_circuit shieldedWalletMintInputs where
  public domain : Bytes32
  private nonce : Bytes32
  public amount : UInt 64
  public recipient : Bytes32
end

noctium_contract ShieldedWalletMint where
  cell minted : struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry mintToWallet uses shieldedWalletMintInputs where
    readSelf as own
    mintShielded(domain, amount)
    writeShieldedCoinCell(minted, disclose(nonce),
      disclose(persistentHashVector32([
        bytes32("midnight:derive_token"), domain, own])),
      cast(UInt 128, amount), false, disclose(recipient))
    return coinNonce : Bytes32 := disclose(nonce)
    return color : Bytes32 := disclose(persistentHashVector32([
      bytes32("midnight:derive_token"), domain, own]))
    return value : UInt 64 := amount
  end
end
