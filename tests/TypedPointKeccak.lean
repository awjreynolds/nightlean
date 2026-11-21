import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit pointHash where
  private point : Secp256k1Point
  output digest : Bytes32 := disclose(keccak256(point))
end

noctium_contract TypedPointKeccak where
  entry hash uses pointHash where
    return pointHashResult : Bytes32 := digest
  end
end
