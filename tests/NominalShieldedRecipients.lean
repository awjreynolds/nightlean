/- Minimal proof that source-only nominal Bytes32 outputs guide recipient checks
while remaining ordinary byte expressions in the Lean and native plans. -/
import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

/-- Nominal source identities use a canonical one-field Bytes32 wire codec.
The marker only guides frontend checks. IR and native plans stay Bytes32. -/
private def contractAddressWire : Helpers.Wire.Codec := {
  payload := .structure "Noctium.Midnight.ContractAddress"
  frameBytes := 32
  composites := {structures := [{
    id := "Noctium.Midnight.ContractAddress"
    fields := [{name := "bytes", type := .bytes 32}]
  }]}
}

private def zswapCoinPublicKeyWire : Helpers.Wire.Codec := {
  payload := .structure "Noctium.Midnight.ZswapCoinPublicKey"
  frameBytes := 32
  composites := {structures := [{
    id := "Noctium.Midnight.ZswapCoinPublicKey"
    fields := [{name := "bytes", type := .bytes 32}]
  }]}
}

noctium_witness_circuit nominalUserRecipient using zswapCoinPublicKeyWire where
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  private enabled : Bool
  private publicKey : Payload zswapCoinPublicKeyWire
  output userRecipient : Bytes32 := disclose(encode(zswapCoinPublicKeyWire, publicKey))
end

noctium_witness_circuit nominalContractRecipient using contractAddressWire where
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  private opening : Native
  private target : Payload contractAddressWire
  output contractTarget : Bytes32 := disclose(encode(contractAddressWire, target))
end

noctium_circuit destinationReceiveInputs where
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_contract NominalRecipientDestination where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry receive uses destinationReceiveInputs arguments [nonce, color, amount] where
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), disclose(amount))
  end
end

noctium_contract NominalShieldedRecipients where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry send uses nominalUserRecipient arguments [nonce, color, amount, enabled, publicKey] where
    sendShieldedFromMap(pot, disclose(nonce), disclose(amount), userRecipient)
  end

  entry relay uses nominalContractRecipient arguments [nonce, color, amount, opening, target] where
    relayShieldedImmediate(disclose(nonce), disclose(color), disclose(amount), contractTarget)
    claimContractCall(contractTarget, disclose(callCommitment(NominalRecipientDestination,
      "receive", opening,
      [shieldedOutputNonce(nonce), color, amount], [])))
  end

end

private def nominalSendEntry : Entrypoint :=
  match NominalShieldedRecipients.entrypoints with
  | selected :: _ => selected
  | [] => {name := "missing", circuit := {name := "missing"}}

private def nominalRelayEntry : Entrypoint :=
  match NominalShieldedRecipients.entrypoints with
  | _ :: selected :: _ => selected
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match nominalSendEntry.effects with
  | effects => effects.any fun effect =>
      match effect with
      | .sendShieldedFromMap _ _ _ _ _ recipient _ =>
          match recipient with
          | .ref "userRecipient" => _root_.Bool.true
          | _ => _root_.Bool.false
      | _ => _root_.Bool.false

#guard match nominalRelayEntry.effects with
  | effects => effects.any fun effect =>
      match effect with
      | .relayShieldedImmediate _ _ _ recipient _ =>
          match recipient with
          | .ref "contractTarget" => _root_.Bool.true
          | _ => _root_.Bool.false
      | _ => _root_.Bool.false

#guard (Disclosure.entrypoint nominalSendEntry).isOk
#guard (Disclosure.entrypoint nominalRelayEntry).isOk

/-- sendShieldedFromMap expects ZswapCoinPublicKey, got ContractAddress -/
#guard_msgs (substring := true) in
noctium_contract WrongUserRecipientNominal where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry send uses nominalContractRecipient arguments [nonce, color, amount, opening, target] where
    sendShieldedFromMap(pot, disclose(nonce), disclose(amount), contractTarget)
  end
end

/-- relayShieldedImmediate expects ContractAddress, got ZswapCoinPublicKey -/
#guard_msgs (substring := true) in
noctium_contract WrongContractRecipientNominal where
  entry relay uses nominalUserRecipient arguments [nonce, color, amount, enabled, publicKey] where
    relayShieldedImmediate(disclose(nonce), disclose(color), disclose(amount), userRecipient)
  end
end

/-- unknown Noctium value 'branchRecipient' -/
#guard_msgs (substring := true) in
noctium_contract IsolatePostBranchNominalRecipient where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry send uses nominalUserRecipient arguments [nonce, color, amount, enabled, publicKey] where
    if enabled then {
      readSelf as branchRecipient
    } else {}
    sendShieldedFromMap(pot, disclose(nonce), disclose(amount), branchRecipient)
  end
end
