import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit relayInputs where
  public domain : Bytes32
  public recipient : Bytes32
  private nonce : Bytes32
  private color : Bytes32
  private opening : Native
end

noctium_circuit destinationReceiveInputs where
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
end

noctium_contract ShieldedImmediateDestination where
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

noctium_contract ShieldedImmediateRelay where
  entry forward uses relayInputs where
    mintShielded(disclose(domain), 5)
    relayShieldedImmediate(disclose(nonce), disclose(color), 5, recipient)
    claimContractCall(recipient, disclose(callCommitment(ShieldedImmediateDestination,
      "receive", opening,
      [shieldedOutputNonce(nonce), color, 5], [])))
  end
end

private def relayForwardEntry : Entrypoint :=
  match ShieldedImmediateRelay.entrypoints with
  | found :: _ => found
  | [] => {name := "missing", circuit := {name := "missing"}}

#guard relayForwardEntry.effects.length == 4
#guard relayForwardEntry.effectGuards.length == 4 &&
  relayForwardEntry.effectGuards.all Option.isNone
#guard match relayForwardEntry.effects with
  | [.mintShielded .., .readContractAddress _, .relayShieldedImmediate ..,
      .claimContractCall ..] => Bool.true
  | _ => Bool.false
#guard (Disclosure.entrypoint relayForwardEntry).isOk
#guard (relayForwardEntry.validate Capabilities.source ShieldedImmediateRelay.state).isOk

#guard match Backend.Impact.lower ShieldedImmediateRelay.state relayForwardEntry with
  | .ok plan =>
      match plan.operations.drop 4 with
      | [.mintShielded .., .readContractAddress _, relayOp, callOp] =>
          match relayOp, callOp with
          | .relayShieldedImmediate _ _ _ (.ref relayName) _ _ _,
            .claimContractCall (.ref callName) _ _ =>
              relayName == "recipient" && relayName == callName &&
              (Backend.Impact.Op.fieldGroups relayOp).length == 18
          | _, _ => Bool.false
      | _ => Bool.false
  | .error _ => Bool.false
