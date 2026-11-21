import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit fundedShieldedReceiveInputs where
  public domain : Bytes32
  private nonce : Bytes32
  private color : Bytes32
end

noctium_contract FundedShieldedReceive where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }
  cell held : struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }
  set registry : struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }
  list coinList : struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry tip uses fundedShieldedReceiveInputs where
    mintShielded(domain, 5)
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), 5)
    writeShieldedCoinCell(held, disclose(nonce), disclose(color), 5)
    insertShieldedCoinSet(registry, disclose(nonce), disclose(color), 5)
    pushFrontCoin(coinList, disclose(nonce), disclose(color), 5)
  end
end
