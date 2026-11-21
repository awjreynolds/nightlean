import Noctium.Backend.Impact
import Noctium.Compiler
import Noctium.ShieldedBurn

open Lean
open Noctium
open scoped Noctium

private def shieldedBurnValueFixture : Entrypoint := {
  name := "shieldedBurnAddress"
  circuit := {
    name := "shieldedBurnAddress"
    outputs := [
      {name := "is_left", ty := .bool,
        value := .bool shieldedBurnAddress.walletBranch},
      {name := "recipient", ty := .bytes 32,
        value := shieldedBurnAddress.recipient}
    ]
  }
}

private def shieldedBurnFixturePlan : Except String Json := do
  let plan ← (Backend.Impact.lower [] shieldedBurnValueFixture).mapError (·.message)
  pure (Compiler.nativePlanJson TargetProfile.selected321 `ShieldedBurnAddress
    [] none shieldedBurnValueFixture plan)

#guard shieldedBurnAddress.walletBranch
#guard match shieldedBurnAddress.recipient with
  | .bytes32Literal bytes => bytes == List.replicate 32 0
  | _ => _root_.Bool.false

#guard match shieldedBurnFixturePlan with
  | .ok plan =>
      match (plan.getObjVal? "circuit").toOption with
      | some circuit =>
          match (circuit.getObjVal? "outputs").toOption with
          | some (.arr outputs) =>
              match outputs[0]?, outputs[1]? with
              | some isLeft, some recipient =>
                  isLeft.getObjValD "expression" == Lean.Json.mkObj [
                    ("tag", toJson ("bool" : String)),
                    ("value", toJson (_root_.Bool.true))] &&
                  recipient.getObjValD "expression" == Lean.Json.mkObj [
                    ("tag", toJson ("bytes32Literal" : String)),
                    ("values", toJson (List.replicate 32 (0 : Nat)))]
              | _, _ => _root_.Bool.false
          | _ => _root_.Bool.false
      | none => _root_.Bool.false
  | .error _ => _root_.Bool.false

noctium_circuit shieldedBurnInputs where
  private nonce : Bytes32
  private color : Bytes32
  private amount : UInt 128
  output burnKey : Bytes32 := shieldedBurnKey()
end

/-- error: relayShieldedImmediate expects ContractAddress, got ZswapCoinPublicKey -/
#guard_msgs (substring := true) in
noctium_contract WrongShieldedBurnAddress where
  entry relay uses shieldedBurnInputs where
    relayShieldedImmediate(disclose(nonce), disclose(color), disclose(amount), shieldedBurnKey())
  end
end
