import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit qualifiedCoinCellInputs where
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_contract QualifiedCoinCell where
  cell coinSlot : struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry writeCoin uses qualifiedCoinCellInputs where
    writeShieldedCoinCell(coinSlot, disclose(nonce), disclose(color), disclose(amount))
  end
end

private def qualifiedCoinCellEntry : Entrypoint :=
  match QualifiedCoinCell.entrypoints with
  | found :: _ => found
  | [] => {name := "missing", circuit := {name := "missing"}}

#guard qualifiedCoinCellEntry.name == "writeCoin"
#guard qualifiedCoinCellEntry.effects.length == 2
#guard qualifiedCoinCellEntry.effectGuards.length == 2 &&
  qualifiedCoinCellEntry.effectGuards.all Option.isNone
#guard match qualifiedCoinCellEntry.effects with
  | [.readContractAddress addressName,
      .writeShieldedCoinCell "coinSlot" _ _ _ (.ref selfAddressName)] =>
      addressName == "noctium_coin_cell_address_0" && addressName == selfAddressName
  | _ => Bool.false
#guard (Disclosure.entrypoint qualifiedCoinCellEntry).isOk
#guard (qualifiedCoinCellEntry.validate Capabilities.source QualifiedCoinCell.state).isOk

#guard match QualifiedCoinCell.state with
  | [{kind := .tree (.composite environment recordType), ..}] =>
      match Backend.Impact.recordSchema environment recordType with
      | .ok schema => schema != Lean.Json.null
      | .error _ => Bool.false
  | _ => Bool.false

#guard match Backend.Impact.lower QualifiedCoinCell.state qualifiedCoinCellEntry with
  | .ok plan =>
      let writes := plan.operations.filter fun operation =>
        match operation with
        | .writeShieldedCoinCell .. => Bool.true
        | _ => Bool.false
      match writes with
      | [operation] =>
          plan.operations.length == 2 &&
          operation.fieldGroups.map List.length == [5, 1, 6, 5, 11, 1, 2, 1]
      | _ => Bool.false
  | .error _ => Bool.false

private def qualifiedCoinCellWrongState : List StateDecl :=
  QualifiedCoinCell.state.map fun declaration =>
    {declaration with kind := .cell (.bytes 32)}

#guard match qualifiedCoinCellEntry.validate Capabilities.source qualifiedCoinCellWrongState with
  | .error diagnostic => diagnostic.message.contains "root composite Cell"
  | .ok _ => Bool.false

private def qualifiedCoinCellGuarded : Entrypoint :=
  {qualifiedCoinCellEntry with effectGuards := [none, some (.bool Bool.true)]}

#guard match qualifiedCoinCellGuarded.validate Capabilities.source QualifiedCoinCell.state with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard (Backend.Zkir.lowerPrunedEntrypoint QualifiedCoinCell.state qualifiedCoinCellEntry).isOk
