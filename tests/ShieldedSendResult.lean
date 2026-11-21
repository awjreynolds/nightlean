import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Frontend
import Noctium.Midnight.ShieldedSendResult

open scoped Noctium
open Noctium

private def shieldedSendResultWire : Helpers.Wire.Codec :=
  Noctium.Midnight.ShieldedSendResult.codec

noctium_witness_circuit shieldedSendResultInputs using shieldedSendResultWire where
  private result : Payload shieldedSendResultWire
  output encodedResult : Bytes 161 := disclose(encode(shieldedSendResultWire, result))
end

noctium_contract ShieldedSendResultFixture where
  entry inspect uses shieldedSendResultInputs arguments [result] where
    return serializedResult : Bytes 161 := encodedResult
  end
end

private def sendResultEnvironment := Noctium.Midnight.ShieldedSendResult.environment
private def sendResultType := Noctium.Midnight.ShieldedSendResult.type
private def sendResultId := Noctium.Midnight.ShieldedSendResult.id
private def coinId := Noctium.Midnight.ShieldedCoinInfo.id
private def coinMaximum := 2 ^ 128 - 1

private def coinValue (nonceByte colorByte amount : Nat) : Types.AggregateValue :=
  .structure coinId [
    ("nonce", .bytes (List.replicate 32 nonceByte)),
    ("color", .bytes (List.replicate 32 colorByte)),
    ("value", .scalar (.uint coinMaximum) amount)]

private def sendResultValue (change sent : Types.AggregateValue) : Types.AggregateValue :=
  .structure sendResultId [("change", change), ("sent", sent)]

private def checkedResult (value : Types.AggregateValue) : _root_.Bool :=
  match Types.compileType sendResultEnvironment sendResultType with
  | .ok compiled => (Types.checkValue compiled value).isOk
  | .error _ => _root_.Bool.false

#guard Noctium.Midnight.ShieldedSendResult.frameBytes == 161
#guard Noctium.Midnight.ShieldedSendResult.fields.map (·.name) == ["change", "sent"]
#guard Noctium.Midnight.ShieldedSendResult.changeFields.map (·.name) == ["is_some", "value"]

#guard match Types.compileType sendResultEnvironment sendResultType with
  | .ok compiled =>
      match Helpers.Wire.declarations compiled "ShieldedSendResult"
          Noctium.Midnight.ShieldedSendResult.frameBytes ⟨0, 1⟩ ⟨0, 2⟩ with
      | .ok [_, _] => Bool.true
      | _ => Bool.false
  | .error _ => Bool.false

private def sentCoin := coinValue 17 23 coinMaximum
private def changedCoin := coinValue 29 31 4
private def presentChange :=
  Noctium.Midnight.ShieldedSendResult.changeValue _root_.Bool.true changedCoin
private def absentChange :=
  Noctium.Midnight.ShieldedSendResult.changeValue _root_.Bool.false changedCoin
private def rawNoncanonicalAbsentChange : Types.AggregateValue := .structure
  Noctium.Midnight.ShieldedSendResult.changeId [
    ("is_some", .scalar .bool 0), ("value", changedCoin)]
private def absentResult := sendResultValue absentChange sentCoin
private def presentResult := sendResultValue presentChange sentCoin
private def rawNoncanonicalAbsentResult := sendResultValue rawNoncanonicalAbsentChange sentCoin

#guard checkedResult absentResult
#guard checkedResult presentResult
#guard checkedResult rawNoncanonicalAbsentResult
#guard absentChange == .structure Noctium.Midnight.ShieldedSendResult.changeId [
  ("is_some", .scalar .bool 0),
  ("value", Noctium.Midnight.ShieldedCoinInfo.zeroValue)]
#guard rawNoncanonicalAbsentChange != absentChange
#guard presentChange == .structure Noctium.Midnight.ShieldedSendResult.changeId [
  ("is_some", .scalar .bool 1), ("value", changedCoin)]
#guard !checkedResult (.structure sendResultId [("sent", sentCoin), ("change", absentChange)])

#guard match ShieldedSendResultFixture.entrypoints with
  | [compiledEntry] =>
      (compiledEntry.validate Capabilities.source ShieldedSendResultFixture.state).isOk &&
        (Backend.Impact.lower ShieldedSendResultFixture.state compiledEntry).isOk
  | _ => Bool.false
