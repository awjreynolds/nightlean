import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Frontend
import Noctium.Midnight.ShieldedCoinInfo

open scoped Noctium
open Noctium

private def shieldedCoinInfoWire : Helpers.Wire.Codec :=
  Noctium.Midnight.ShieldedCoinInfo.codec

noctium_witness_circuit shieldedCoinInfoInputs using shieldedCoinInfoWire where
  private coin : Payload shieldedCoinInfoWire
  output encodedCoin : Bytes 80 := disclose(encode(shieldedCoinInfoWire, coin))
end

noctium_contract ShieldedCoinInfoWireFixture where
  entry inspect uses shieldedCoinInfoInputs arguments [coin] where
    return serializedCoin : Bytes 80 := encodedCoin
  end
end

private def shieldedCoinInfoType := Noctium.Midnight.ShieldedCoinInfo.type
private def shieldedCoinInfoEnvironment := Noctium.Midnight.ShieldedCoinInfo.environment
private def shieldedCoinInfoMaximum := 2 ^ 128 - 1

#guard Noctium.Midnight.ShieldedCoinInfo.frameBytes == 80
#guard Noctium.Wire.scalarWidth (.bytes 32) == some 32
#guard Noctium.Wire.scalarWidth (.uint shieldedCoinInfoMaximum) == some 16

#guard match Types.compileType shieldedCoinInfoEnvironment shieldedCoinInfoType with
  | .ok compiled =>
      match Helpers.Wire.declarations compiled "ShieldedCoinInfo"
          Noctium.Midnight.ShieldedCoinInfo.frameBytes ⟨0, 1⟩ ⟨0, 2⟩ with
      | .ok [_, _] => Bool.true
      | _ => Bool.false
  | .error _ => Bool.false

#guard match ShieldedCoinInfoWireFixture.entrypoints with
  | [compiledEntry] =>
      (compiledEntry.validate Capabilities.source ShieldedCoinInfoWireFixture.state).isOk &&
        (Backend.Impact.lower ShieldedCoinInfoWireFixture.state compiledEntry).isOk
  | _ => Bool.false

private def coinFields (value : Nat) : List (String × Types.AggregateValue) := [
  ("nonce", .bytes (List.range 32)),
  ("color", .bytes (List.replicate 32 255)),
  ("value", .scalar (.uint shieldedCoinInfoMaximum) value)
]

private def validCoinFields (fields : List (String × Types.AggregateValue)) : _root_.Bool :=
  match Types.compileType shieldedCoinInfoEnvironment shieldedCoinInfoType with
  | .ok compiled =>
    (Types.checkValue compiled (.structure Noctium.Midnight.ShieldedCoinInfo.id fields)).isOk
  | .error _ => Bool.false

#guard validCoinFields (coinFields 0)
#guard validCoinFields (coinFields shieldedCoinInfoMaximum)
#guard !validCoinFields (coinFields (shieldedCoinInfoMaximum + 1))
#guard !validCoinFields (coinFields 0).reverse
#guard !validCoinFields (coinFields 0 ++ [("mtIndex", .scalar (.uint (2 ^ 64 - 1)) 0)])
