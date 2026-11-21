import Noctium.Compiler
import Noctium.Frontend

open scoped Noctium
open Noctium

namespace OwnPublicKeyWitnessFixture

private def zswapCoinPublicKeyWire : Helpers.Wire.Codec := {
  payload := .structure "Noctium.Midnight.ZswapCoinPublicKey"
  frameBytes := 32
  composites := {structures := [{
    id := "Noctium.Midnight.ZswapCoinPublicKey"
    fields := [{name := "bytes", type := .bytes 32}]
  }]}
}

noctium_witness ownPublicKey() : Payload zswapCoinPublicKeyWire

noctium_witness_circuit exposeOwnPublicKey using zswapCoinPublicKeyWire where
  let key := witness ownPublicKey()
  output publicKey : Bytes32 := disclose(encode(zswapCoinPublicKeyWire, key))
end

noctium_contract OwnPublicKeyWitness where
  cell registeredKey : Bytes32

  entry capture uses exposeOwnPublicKey where
    write registeredKey := publicKey
  end
end

/-- undisclosed private provider result 'OwnPublicKeyWitnessFixture.ownPublicKey' -/
#guard_msgs (substring := true) in
noctium_witness_circuit leakOwnPublicKey using zswapCoinPublicKeyWire where
  let key := witness ownPublicKey()
  output publicKey : Bytes32 := encode(zswapCoinPublicKeyWire, key)
end

end OwnPublicKeyWitnessFixture
