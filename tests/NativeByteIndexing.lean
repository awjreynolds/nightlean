import Noctium.Frontend

open scoped Noctium

noctium_circuit computedByteIndexing where
  private payload : Bytes32
  private field : Native
  public chooseHash : Bool
  let digest : Bytes32 := persistentHash32(payload)
  output rawFirst : UInt 8 := disclose(byteAt(payload, 0))
  output digestFirst : UInt 8 := disclose(byteAt(digest, 0))
  output digestLast : UInt 8 := disclose(byteAt(digest, 31))
  output serializedSecond : UInt 8 := disclose(byteAt(toBytes32(field), 1))
  output selectedByte : UInt 8 := disclose(byteAt(select(chooseHash, digest, toBytes32(field)), 7))
end

noctium_contract NativeByteIndexing where
  cell rawFirst : UInt 8
  cell digestFirst : UInt 8
  cell digestLast : UInt 8
  cell serializedSecond : UInt 8
  cell selectedByte : UInt 8
  entry inspect uses computedByteIndexing where
    write rawFirst := rawFirst
    write digestFirst := digestFirst
    write digestLast := digestLast
    write serializedSecond := serializedSecond
    write selectedByte := selectedByte
  end
end

-- Selecting a digest byte retains its private source origin.
#guard !(Nightlean.Disclosure.circuit {
  name := "byteLeak"
  inputs := [{name := "payload", ty := .bytes 32, visibility := .private}]
  outputs := [{name := "leaked", ty := .uint 255, value := .bytesAt (.persistentHash32 (.ref "payload")) 0}]
}).isOk
