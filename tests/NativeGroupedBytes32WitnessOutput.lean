import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_witness_circuit groupedAccount where
  private accountSecret : Bytes32
  public expectedAccountId : Bytes32
  public count : UInt 8
  let accountDigest : Bytes32 := persistentHash32(accountSecret)
  prove eq(expectedAccountId, accountDigest)
  output accountId : Bytes32 := disclose(accountDigest)
  output countValue : UInt 8 := count
end

noctium_contract NativeGroupedBytes32WitnessOutput where
  map registered : Bytes32 => UInt 8
  entry register uses groupedAccount where
    insert registered[accountId] := countValue
    read registered[accountId] as storedCount
    require eq(storedCount, countValue)
  end
end
