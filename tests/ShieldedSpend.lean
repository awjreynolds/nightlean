import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.Disclosure
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit shieldedSpendReceiveInputs where
  public domain : Bytes32
  private nonce : Bytes32
  private color : Bytes32
end

noctium_circuit shieldedSpendInputs where
  private nonce : Bytes32
  private recipient : Bytes32
end

noctium_contract ShieldedSpend where
  tree pot : Bytes32 => struct Coin {
    nonce : Bytes32
    color : Bytes32
    value : UInt 128
    mtIndex : UInt 64
  }

  entry tip uses shieldedSpendReceiveInputs where
    mintShielded(domain, 5)
    receiveShieldedToMap(pot, disclose(nonce), disclose(color), 5)
  end

  entry spend uses shieldedSpendInputs where
    spendShieldedFromMap(pot, disclose(nonce), disclose(recipient))
  end
end

private def shieldedSpendReceiveEntry : Entrypoint :=
  match ShieldedSpend.entrypoints with
  | found :: _ => found
  | [] => {name := "missing", circuit := {name := "missing"}}

private def shieldedSpendEntry : Entrypoint :=
  match ShieldedSpend.entrypoints with
  | _ :: found :: _ => found
  | _ => {name := "missing", circuit := {name := "missing"}}

private def isReference {ty : Ty} (value : Expr ty) (name : String) : _root_.Bool :=
  match value with
  | .ref found => found == name
  | _ => _root_.Bool.false

private def isDisclosedReference {ty : Ty} (value : Expr ty) (name : String) : _root_.Bool :=
  match value with
  | .disclose _ released => isReference released name
  | _ => _root_.Bool.false

private def spendsRecordedCoin (effect : Effect) : _root_.Bool :=
  match effect with
  | .spendShieldedFromMap state nonce color amount recipient address =>
        state == "pot" &&
        isReference nonce "noctium_spend_coin_0_nonce" &&
        isReference color "noctium_spend_coin_0_color" &&
        isReference amount "noctium_spend_coin_0_value" &&
        isDisclosedReference recipient "recipient" &&
        isReference address "noctium_spend_address_2"
  | _ => _root_.Bool.false

#guard shieldedSpendReceiveEntry.name == "tip"
#guard shieldedSpendEntry.name == "spend"
#guard match shieldedSpendReceiveEntry.effects with
  | [.mintShielded .., .memberPath "pot" _ [_], .require _,
      .readContractAddress _, .receiveShieldedToMap "pot" ..] => _root_.Bool.true
  | _ => _root_.Bool.false
#guard shieldedSpendEntry.effects.length == 5
#guard shieldedSpendEntry.effectGuards.length == 5 &&
  shieldedSpendEntry.effectGuards.all Option.isNone
#guard match shieldedSpendEntry.effects with
  | [.readCompositePath "pot" _ [_] _ fields, .require _,
      .readContractAddress _, spend, .removePath "pot" [_]] =>
        fields.map Prod.fst == [
          "noctium_spend_coin_0_nonce",
          "noctium_spend_coin_0_color",
          "noctium_spend_coin_0_value",
          "noctium_spend_coin_0_mtIndex"] &&
        fields.map Prod.snd == [Ty.bytes 32, Ty.bytes 32,
          Ty.uint (2 ^ 128 - 1), Ty.uint (2 ^ 64 - 1)] &&
        spendsRecordedCoin spend
  | _ => _root_.Bool.false
#guard (Disclosure.entrypoint shieldedSpendEntry).isOk
#guard (shieldedSpendEntry.validate Capabilities.source ShieldedSpend.state).isOk

private def spendBytes (byte : Nat) : Value := .bytes 32 (List.replicate 32 byte)

private def spendInputs : EvalEnv := [
  ("nonce", spendBytes 1),
  ("recipient", spendBytes 2)]

private def spendState (recordNonce : Nat) : LedgerState := {
  trees := [("pot", .map [
    (spendBytes 1, .composite (.structure "ShieldedSpend.Coin") [
      spendBytes recordNonce,
      spendBytes 3,
      .uint (2 ^ 128 - 1) 5,
      .uint (2 ^ 64 - 1) 0])])]
}

private def spendContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by shielded spend fixture"
  ownContractAddress := some (List.replicate 32 4)
}

#guard match Entrypoint.run spendContext shieldedSpendEntry spendInputs (spendState 2) with
  | .error message => message == "state transition guard failed"
  | .ok _ => _root_.Bool.false
#guard match Entrypoint.run spendContext shieldedSpendEntry spendInputs (spendState 1) with
  | .error message =>
      message == "reference evaluator cannot determine the native shielded spend commitment"
  | .ok _ => _root_.Bool.false
