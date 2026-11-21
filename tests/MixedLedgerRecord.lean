import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit mixedLedgerRecordInputs where
  private owner : Bytes32
  private account : Bytes32
  private amount : Native
  private payload : Bytes32
  private recipient : JubjubPoint
  public enabled : Bool
end

noctium_contract MixedLedgerRecord where
  tree records : Bytes32 => struct Record {
    amount : Native
    payload : Bytes32
    recipient : JubjubPoint
  }
  tree nestedRecords : Bytes32 => Bytes32 => struct Record {
    amount : Native
    payload : Bytes32
    recipient : JubjubPoint
  }
  list history : struct Record {
    amount : Native
    payload : Bytes32
    recipient : JubjubPoint
  }

  entry append uses mixedLedgerRecordInputs where
    write records[disclose(account)] := fields(
      disclose(amount), disclose(payload), disclose(recipient))
    read records[disclose(account)] as direct
    member nestedRecords[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert nestedRecords[disclose(owner)] := emptyMap
    } else {
    }
    write nestedRecords[disclose(owner)][disclose(account)] := fields(
      disclose(amount), disclose(payload), disclose(recipient))
    read nestedRecords[disclose(owner)][disclose(account)] as nested
    pushFront history := fields(disclose(amount), disclose(payload), disclose(recipient))
    headOrDefault history as (historyPresent, head)
    return directAmount : Native := disclose(direct_amount)
    return directPayload : Bytes32 := disclose(direct_payload)
    return directRecipient : JubjubPoint := disclose(direct_recipient)
    return nestedAmount : Native := disclose(nested_amount)
    return nestedPayload : Bytes32 := disclose(nested_payload)
    return nestedRecipient : JubjubPoint := disclose(nested_recipient)
    return hasHistory : Bool := historyPresent
    return headAmount : Native := disclose(head_amount)
    return headPayload : Bytes32 := disclose(head_payload)
    return headRecipient : JubjubPoint := disclose(head_recipient)
  end

  entry guarded uses mixedLedgerRecordInputs where
    when enabled member records[disclose(account)] as recordPresent
    when enabled member nestedRecords[disclose(owner)][disclose(account)] as nestedPresent
    when enabled read records[disclose(account)] as direct
    when enabled read nestedRecords[disclose(owner)][disclose(account)] as nested
    when enabled headOrDefault history as (historyPresent, head)
    return present : Bool := recordPresent
    return nestedIsPresent : Bool := nestedPresent
    return hasHistory : Bool := historyPresent
    return directAmount : Native := disclose(direct_amount)
    return directPayload : Bytes32 := disclose(direct_payload)
    return directRecipient : JubjubPoint := disclose(direct_recipient)
    return nestedAmount : Native := disclose(nested_amount)
    return nestedPayload : Bytes32 := disclose(nested_payload)
    return nestedRecipient : JubjubPoint := disclose(nested_recipient)
    return headAmount : Native := disclose(head_amount)
    return headPayload : Bytes32 := disclose(head_payload)
    return headRecipient : JubjubPoint := disclose(head_recipient)
  end

  entry pop uses mixedLedgerRecordInputs where
    popFront history
    headOrDefault history as (historyPresent, head)
    return hasHistory : Bool := historyPresent
    return headAmount : Native := disclose(head_amount)
    return headPayload : Bytes32 := disclose(head_payload)
    return headRecipient : JubjubPoint := disclose(head_recipient)
  end
end

private def mixedLedgerRecordEntry (name : String) : Entrypoint :=
  match MixedLedgerRecord.entrypoints.find? (·.name == name) with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Impact.lower MixedLedgerRecord.state (mixedLedgerRecordEntry "append") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint MixedLedgerRecord.state
    (mixedLedgerRecordEntry "append") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint MixedLedgerRecord.state
    (mixedLedgerRecordEntry "guarded") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Disclosure.entrypoint (mixedLedgerRecordEntry "append") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def mixedLedgerRecordContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
  jubjub := {pointValid := fun point =>
    if point == (0, 1) then .ok () else .error "fixture accepts only the identity"}
}

#guard match Entrypoint.run mixedLedgerRecordContext
    (mixedLedgerRecordEntry "guarded")
    [ ("account", .bytes 32 (List.replicate 32 0))
    , ("owner", .bytes 32 (List.replicate 32 0))
    , ("amount", .native 0)
    , ("payload", .bytes 32 (List.replicate 32 0))
    , ("recipient", .jubjubPoint 0 1)
    , ("enabled", .bool Bool.false)
    ]
    {trees := [
      ("records", .map []),
      ("nestedRecords", .map []),
      ("history", .list [])
    ]} with
  | .ok (outputs, _) =>
      outputs.lookup "present" == some (.bool Bool.false) &&
      outputs.lookup "nestedIsPresent" == some (.bool Bool.false) &&
      outputs.lookup "hasHistory" == some (.bool Bool.false) &&
      outputs.lookup "directAmount" == some (.native 0) &&
      outputs.lookup "directPayload" == some (.bytes 32 (List.replicate 32 0)) &&
      outputs.lookup "directRecipient" == some (.jubjubPoint 0 1) &&
      outputs.lookup "nestedAmount" == some (.native 0) &&
      outputs.lookup "nestedPayload" == some (.bytes 32 (List.replicate 32 0)) &&
      outputs.lookup "nestedRecipient" == some (.jubjubPoint 0 1) &&
      outputs.lookup "headAmount" == some (.native 0) &&
      outputs.lookup "headPayload" == some (.bytes 32 (List.replicate 32 0)) &&
      outputs.lookup "headRecipient" == some (.jubjubPoint 0 1)
  | .error _ => Bool.false

private def hideMixedPayload (value : LedgerFieldExpr) : LedgerFieldExpr :=
  match value with
  | .mk ty (.disclose _ (.ref "payload")) => .mk ty (.ref "payload")
  | other => other

private def mixedLedgerRecordUndisclosedPayload : Entrypoint :=
  let operation := mixedLedgerRecordEntry "append"
  {operation with effects := operation.effects.map fun effect =>
    match effect with
    | .writeCompositePath state keys type values =>
        .writeCompositePath state keys type (values.map hideMixedPayload)
    | other => other}

#guard match Disclosure.entrypoint mixedLedgerRecordUndisclosedPayload with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter 'payload'"
  | .ok _ => Bool.false
