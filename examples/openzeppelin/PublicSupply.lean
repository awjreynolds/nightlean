-- SPDX-License-Identifier: MIT
-- Copyright (c) 2025 Zeppelin Group Ltd
-- Adapted from OpenZeppelin Compact Contracts, ConfidentialFungibleTokenPublicSupply.
-- Reference: f85f1a23685c6bbedfc8c2589ae3aa128aff7c46.
import Noctium.Frontend

open scoped Noctium

namespace OpenZeppelinPort

noctium_circuit supplyDelta where
  private amount : UInt 128
end

-- These accounting blocks must be paired with the token's encrypted mint/burn.
-- They are an ungated benchmark component, not an issuance policy.
-- totalSupply is public ledger state, so its changes reveal each amount.
noctium_contract PublicSupply where
  cell totalSupply : UInt 128
  entry addSupply uses supplyDelta where
    read totalSupply as previous
    write totalSupply := disclose(cast(UInt 128, add(previous, amount)))
  end
  entry subSupply uses supplyDelta where
    read totalSupply as previous
    write totalSupply := disclose(sub(previous, amount))
  end
end

private def supplyTransition (name : String) (total amount : Nat) :
    Except String Noctium.LedgerState := do
  let some ep := PublicSupply.entrypoints.find? (·.name == name)
    | throw "missing entrypoint"
  let (_, next) ← ep.run {
    modulus := Noctium.Field.modulus
    poseidon2 := fun _ _ _ => .error "unused"
  } [("amount", .uint (2 ^ 128 - 1) amount)] {
    cells := [("totalSupply", .uint (2 ^ 128 - 1) total)]
  }
  pure next

#guard match supplyTransition "addSupply" 0 5 with
  | .ok minted => match minted.cells.lookup "totalSupply" with
    | some (.uint _ total) => match supplyTransition "subSupply" total 2 with
      | .ok burned => burned.cells.lookup "totalSupply" == some (.uint (2 ^ 128 - 1) 3)
      | .error _ => Bool.false
    | _ => Bool.false
  | .error _ => Bool.false

#guard (supplyTransition "addSupply" (2 ^ 128 - 1) 1).toOption.isNone
#guard (supplyTransition "subSupply" 0 1).toOption.isNone

end OpenZeppelinPort
