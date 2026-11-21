import Noctium.Backend.Impact
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit immediateMergeInputs where
  public domain : Bytes32
  private nonceA : Bytes32
  private nonceB : Bytes32
  private colorB : Bytes32
end

noctium_contract ShieldedCoinImmediateMerge where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry merge uses immediateMergeInputs where
    mintShielded(domain, 7)
    mergeShieldedImmediateFromMap(pot, disclose(nonceA), disclose(nonceB), disclose(colorB), 7)
  end
end

#guard match ShieldedCoinImmediateMerge.entrypoints with
  | [found] =>
    (Disclosure.entrypoint found).isOk &&
      match Backend.Impact.lower ShieldedCoinImmediateMerge.state found with
      | .ok plan =>
        match plan.operations.filter (fun operation =>
          match operation with
          | .mergeShieldedFromMap .. | .mapRemove .. | .receiveShieldedToMap .. => Bool.true
          | _ => Bool.false) with
        | [merge@(.mergeShieldedFromMap _ _ _ _ _ _ _ _ _ _ _ _ (some _)),
            .mapRemove sourceSlot _, .receiveShieldedToMap outputSlot ..] =>
          sourceSlot == outputSlot && merge.fieldGroups.length == 24
        | _ => Bool.false
      | .error _ => Bool.false
  | _ => Bool.false
