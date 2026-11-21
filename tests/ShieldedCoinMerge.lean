import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit mergeShieldedInputs where
  private nonceA : Bytes32
  private nonceB : Bytes32
end

noctium_circuit mergeShieldedMintInputs where
  public domain : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 64
end

noctium_contract ShieldedCoinMerge where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry mint uses mergeShieldedMintInputs where
    mintShielded(domain, disclose(amount))
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), disclose(amount))
  end

  entry merge uses mergeShieldedInputs arguments [nonceA, nonceB] where
    mergeShieldedFromMap(pot, disclose(nonceA), disclose(nonceB))
  end
end

private def mergeEntry : Entrypoint :=
  ShieldedCoinMerge.entrypoints.find? (·.name == "merge") |>.getD
    {name := "missing", circuit := {name := "missing"}}

private def mintEntry : Entrypoint :=
  ShieldedCoinMerge.entrypoints.find? (·.name == "mint") |>.getD
    {name := "missing", circuit := {name := "missing"}}

#guard mergeEntry.name == "merge"
#guard mintEntry.name == "mint"
#guard (Disclosure.entrypoint mintEntry).isOk
#guard (mintEntry.validate Capabilities.source ShieldedCoinMerge.state).isOk
#guard (Disclosure.entrypoint mergeEntry).isOk
#guard (mergeEntry.validate Capabilities.source ShieldedCoinMerge.state).isOk

#guard match mergeEntry.effects with
  | [ .readCompositePath "pot" _ [_] _ fieldsA, .require _,
      .readCompositePath "pot" _ [_] _ fieldsB, .require _, .require _, .require _,
      .readContractAddress _, .memberPath "pot" _ [_], .require _,
      .mergeShieldedFromMap "pot" ..,
      .removePath "pot" [_], .removePath "pot" [_],
      .receiveShieldedToMap "pot" ..] =>
        fieldsA.map Prod.fst == [
          "noctium_merge_coin_0_nonce",
          "noctium_merge_coin_0_color",
          "noctium_merge_coin_0_value",
          "noctium_merge_coin_0_mtIndex"] &&
        fieldsB.map Prod.fst == [
          "noctium_merge_coin_2_nonce",
          "noctium_merge_coin_2_color",
          "noctium_merge_coin_2_value",
          "noctium_merge_coin_2_mtIndex"]
  | _ => _root_.Bool.false

#guard match Backend.Impact.lower ShieldedCoinMerge.state mergeEntry with
  | .ok plan =>
      match plan.operations.filter (fun operation =>
        match operation with
        | .mergeShieldedFromMap .. | .mapRemove .. | .receiveShieldedToMap .. => _root_.Bool.true
        | _ => _root_.Bool.false) with
      | [.mergeShieldedFromMap .., .mapRemove firstSlot _, .mapRemove secondSlot _,
          .receiveShieldedToMap receiveSlot ..] =>
            firstSlot == secondSlot && secondSlot == receiveSlot &&
            (plan.operations.find? fun operation =>
              match operation with
              | .mergeShieldedFromMap .. => _root_.Bool.true
              | _ => _root_.Bool.false).map (·.fieldGroups.length) == some 18 &&
            (plan.operations.find? fun operation =>
              match operation with
              | .receiveShieldedToMap .. => _root_.Bool.true
              | _ => _root_.Bool.false).map (·.fieldGroups.length) == some 16
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false

private def mergePlanJson : Except String Lean.Json := do
  let plan ← (Backend.Impact.lower ShieldedCoinMerge.state mergeEntry).mapError (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321 `ShieldedCoinMerge
    ShieldedCoinMerge.state none mergeEntry plan)

#guard match mergePlanJson with
  | .ok plan =>
      match (plan.getObjVal? "operations").toOption with
      | some (.arr operations) =>
          operations.any fun operation =>
            operation.getObjValD "op" == Lean.toJson ("mergeShieldedFromMap" : String) &&
            (operation.getObjVal? "nullifierA").isOk &&
            (operation.getObjVal? "nullifierB").isOk &&
            (operation.getObjVal? "outputCommitment").isOk
      | _ => _root_.Bool.false
  | .error _ => _root_.Bool.false
