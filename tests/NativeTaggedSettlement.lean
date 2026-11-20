import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit taggedSettlementInputs where
  public color : Bytes32
  public amount : UInt 128
  public extra : UInt 128
  private isUnshielded : Bool
  public isContract : Bool
  public recipient : Bytes32
  public enabled : Bool
  public addSecond : Bool
end

noctium_circuit taggedSettleInputs where
  public domain : Bytes32
end

noctium_contract NativeTaggedSettlement where
  entry record uses taggedSettlementInputs where
    when enabled incUnshieldedInputs(color, amount, disclose(isUnshielded))
    when enabled incUnshieldedOutputs(color, amount, disclose(isUnshielded))
    when enabled claimUnshieldedCoinSpend(color, amount, disclose(isUnshielded), isContract, recipient)
    when addSecond incUnshieldedInputs(color, extra, disclose(isUnshielded))
    when addSecond incUnshieldedOutputs(color, extra, disclose(isUnshielded))
    when addSecond claimUnshieldedCoinSpend(color, extra, disclose(isUnshielded), isContract, recipient)
  end
  entry settle uses taggedSettleInputs where
    readSelf as own
    mintUnshielded(domain, 17)
    mintShielded(domain, 23)
    incUnshieldedOutputs(persistentHashVector32([
      bytes32("midnight:derive_token"), domain, own]), 7, true)
    claimUnshieldedCoinSpend(persistentHashVector32([
      bytes32("midnight:derive_token"), domain, own]), 24, true, true, own)
    incUnshieldedInputs(persistentHashVector32([
      bytes32("midnight:derive_token"), domain, own]), 24, true)
    incUnshieldedOutputs(persistentHashVector32([
      bytes32("midnight:derive_token"), domain, own]), 7, false)
    claimUnshieldedCoinSpend(persistentHashVector32([
      bytes32("midnight:derive_token"), domain, own]), 30, false, true, own)
    incUnshieldedInputs(persistentHashVector32([
      bytes32("midnight:derive_token"), domain, own]), 30, false)
    tokenBalance(persistentHashVector32([
      bytes32("midnight:derive_token"), domain, own]), true) as priorUnshielded
    tokenBalance(persistentHashVector32([
      bytes32("midnight:derive_token"), domain, own]), false) as priorShielded
    require eq(priorUnshielded, 0)
    require eq(priorShielded, 0)
  end
end

private def taggedSettlementContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
}

private def taggedSettlementArgs (amount extra : Nat)
    (enabled addSecond isUnshielded : _root_.Bool)
    (isContract : _root_.Bool) : EvalEnv := [
  ("color", .bytes 32 (List.range 32)),
  ("amount", .uint balanceMaximum amount),
  ("extra", .uint balanceMaximum extra),
  ("isUnshielded", .bool isUnshielded),
  ("isContract", .bool isContract),
  ("recipient", .bytes 32 (List.replicate 32 9)),
  ("enabled", .bool enabled),
  ("addSecond", .bool addSecond)
]

private def runTaggedRecord (amount extra : Nat)
    (enabled addSecond isUnshielded isContract : _root_.Bool)
    (state : LedgerState := {}) : Except String (EvalEnv × LedgerState) := do
  let some operation := NativeTaggedSettlement.entrypoints.find?
      (fun (candidate : Entrypoint) => candidate.name == "record")
    | throw "missing tagged-record entrypoint"
  operation.run taggedSettlementContext
    (taggedSettlementArgs amount extra enabled addSecond isUnshielded isContract) state

private def taggedKey (isUnshielded : _root_.Bool) : TokenEffectKey := {
  color := List.range 32
  isUnshielded := isUnshielded
}

private def spendKey (color : List Nat) (isUnshielded isContract : _root_.Bool)
    (recipient : List Nat) : SpendClaimKey := {
  color := color
  isUnshielded := isUnshielded
  isContract := isContract
  recipient := recipient
}

private def runTaggedSettle (ctx : EvalContext) (domain : List Nat) (state : LedgerState := {}) :
    Except String (EvalEnv × LedgerState) := do
  let some operation := NativeTaggedSettlement.entrypoints.find?
      (fun (candidate : Entrypoint) => candidate.name == "settle")
    | throw "missing tagged-settle entrypoint"
  operation.run ctx [("domain", .bytes 32 domain)] state

#guard match runTaggedRecord 17 5 Bool.true Bool.true Bool.true Bool.false with
  | .ok (_, state) =>
    state.unshieldedInputs.lookup (taggedKey Bool.true) == some 22 &&
    state.unshieldedOutputs.lookup (taggedKey Bool.true) == some 22 &&
    state.unshieldedSpendClaims.lookup
      (spendKey (List.range 32) Bool.true Bool.false (List.replicate 32 9)) == some 22
  | .error _ => Bool.false

#guard match runTaggedRecord 17 5 Bool.true Bool.false Bool.false Bool.false with
  | .ok (_, state) =>
    state.unshieldedInputs.lookup (taggedKey Bool.false) == some 17 &&
    state.unshieldedOutputs.lookup (taggedKey Bool.false) == some 17 &&
    state.unshieldedSpendClaims.lookup
      (spendKey (List.range 32) Bool.false Bool.false (List.replicate 32 9)) == some 17
  | .error _ => Bool.false

#guard match runTaggedRecord 17 5 Bool.false Bool.false Bool.true Bool.false with
  | .ok (_, state) => state.unshieldedInputs.isEmpty &&
      state.unshieldedOutputs.isEmpty && state.unshieldedSpendClaims.isEmpty
  | .error _ => Bool.false

#guard match runTaggedRecord (2 ^ 64) 1 Bool.true Bool.true Bool.true Bool.false with
  | .error message => message.contains "UInt64 operands"
  | .ok _ => Bool.false

#guard
  let color := List.replicate 32 4
  let recipient := List.replicate 32 8
  let effects : List Effect := [
    .claimUnshieldedCoinSpend (.bytes32Literal color) (.uint balanceMaximum 7)
      (.bool Bool.true) (.bool Bool.false) (.bytes32Literal recipient),
    .claimUnshieldedCoinSpend (.bytes32Literal color) (.uint balanceMaximum 9)
      (.bool Bool.true) (.bool Bool.true) (.bytes32Literal recipient)
  ]
  match runEffects taggedSettlementContext effects [] {} with
  | .ok state =>
    state.unshieldedSpendClaims.length == 2 &&
    state.unshieldedSpendClaims.lookup (spendKey color Bool.true Bool.false recipient) == some 7 &&
    state.unshieldedSpendClaims.lookup (spendKey color Bool.true Bool.true recipient) == some 9
  | .error _ => Bool.false

#guard
  let color := List.replicate 32 42
  let own := List.replicate 32 7
  let domain := List.replicate 32 11
  let ctx : EvalContext := {
    modulus := Field.modulus,
    poseidon2 := fun _ _ _ => .error "unused",
    persistentHash32 := fun _ => .ok color,
    ownContractAddress := some own,
    unshieldedBalances := [(color, 0)],
    shieldedBalances := [(color, 0)]
  }
  let initial : LedgerState := {
    unshieldedMints := [(List.replicate 32 99, 3)],
    unshieldedInputs := [(taggedKey Bool.true, 8)],
    unshieldedOutputs := [(taggedKey Bool.true, 9)],
    unshieldedSpendClaims := [(spendKey (List.range 32) Bool.true Bool.false
      (List.replicate 32 9), 10)]
  }
  match runTaggedSettle ctx domain initial with
  | .ok (_, state) =>
    state.unshieldedMints == [(domain, 17), (List.replicate 32 99, 3)] &&
    state.shieldedMints == [(domain, 23)] &&
    state.unshieldedInputs.lookup {color := color, isUnshielded := Bool.true} == some 24 &&
    state.unshieldedInputs.lookup {color := color, isUnshielded := Bool.false} == some 30 &&
    state.unshieldedOutputs.lookup {color := color, isUnshielded := Bool.true} == some 7 &&
    state.unshieldedOutputs.lookup {color := color, isUnshielded := Bool.false} == some 7 &&
    state.unshieldedSpendClaims.lookup (spendKey color Bool.true Bool.true own) == some 24 &&
    state.unshieldedSpendClaims.lookup (spendKey color Bool.false Bool.true own) == some 30
  | .error _ => Bool.false
