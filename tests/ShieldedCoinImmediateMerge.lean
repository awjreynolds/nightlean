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

noctium_circuit immediateMergeMintInputs where
  public domain : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 64
end

noctium_contract ShieldedCoinImmediateMerge where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry mint uses immediateMergeMintInputs where
    mintShielded(domain, disclose(amount))
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), disclose(amount))
  end

  entry merge uses immediateMergeInputs where
    mintShielded(domain, 7)
    mergeShieldedImmediateFromMap(pot, disclose(nonceA), disclose(nonceB), disclose(colorB), 7)
  end
end

private def immediateMergeEntry : Entrypoint :=
  ShieldedCoinImmediateMerge.entrypoints.find? (·.name == "merge") |>.getD
    {name := "missing", circuit := {name := "missing"}}

private def immediateMintEntry : Entrypoint :=
  ShieldedCoinImmediateMerge.entrypoints.find? (·.name == "mint") |>.getD
    {name := "missing", circuit := {name := "missing"}}

#guard immediateMergeEntry.name == "merge"
#guard immediateMintEntry.name == "mint"
#guard (Disclosure.entrypoint immediateMintEntry).isOk
#guard (Disclosure.entrypoint immediateMergeEntry).isOk
#guard (immediateMintEntry.validate Capabilities.source ShieldedCoinImmediateMerge.state).isOk
#guard (immediateMergeEntry.validate Capabilities.source ShieldedCoinImmediateMerge.state).isOk

#guard match Backend.Impact.lower ShieldedCoinImmediateMerge.state immediateMergeEntry with
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
