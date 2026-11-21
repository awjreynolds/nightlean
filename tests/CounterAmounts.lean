import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit counterAmountInputs where
  private owner : Bytes32
  private spender : Bytes32
  private amount : UInt 16
  public enabled : Bool
end

noctium_contract CounterAmounts where
  counter total
  tree epochs : Bytes32 => Bytes32 => Counter

  entry apply uses counterAmountInputs where
    member epochs[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert epochs[disclose(owner)] := emptyMap
    } else {
    }
    member epochs[disclose(owner)][disclose(spender)] as epochPresent
    if eq(epochPresent, false) then {
      reset epochs[disclose(owner)][disclose(spender)]
    } else {
    }
    increment total by disclose(amount)
    increment epochs[disclose(owner)][disclose(spender)] by disclose(amount)
    read total as totalAfterApply
    read epochs[disclose(owner)][disclose(spender)] as epochAfterApply
    return totalValue : UInt 64 := totalAfterApply
    return epochValue : UInt 64 := epochAfterApply
  end

  entry reduce uses counterAmountInputs where
    decrement total by disclose(amount)
    decrement epochs[disclose(owner)][disclose(spender)] by disclose(amount)
    read total as totalAfterReduce
    read epochs[disclose(owner)][disclose(spender)] as epochAfterReduce
    return totalValue : UInt 64 := totalAfterReduce
    return epochValue : UInt 64 := epochAfterReduce
  end

  entry guarded uses counterAmountInputs where
    when enabled increment epochs[disclose(owner)][disclose(spender)]
      by disclose(assertThen(enabled, amount))
  end
end

private def counterAmountsEntry (name : String) : Entrypoint :=
  match CounterAmounts.entrypoints.find? (·.name == name) with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

private def hasDynamicAmount (entryName : String) (subtract : _root_.Bool) : _root_.Bool :=
  match Backend.Impact.lower CounterAmounts.state (counterAmountsEntry entryName) with
  | .error _ => Bool.false
  | .ok plan =>
      let adjusted := plan.operations.filter fun operation =>
        match operation, subtract with
        | .addImmediate (.cast _ (.disclose _ (.ref "amount"))), Bool.false => Bool.true
        | .subImmediate (.cast _ (.disclose _ (.ref "amount"))), Bool.true => Bool.true
        | _, _ => Bool.false
      adjusted.length == 2

#guard hasDynamicAmount "apply" Bool.false
#guard hasDynamicAmount "reduce" Bool.true

#guard match Backend.Zkir.lowerEntrypoint CounterAmounts.state (counterAmountsEntry "apply") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint CounterAmounts.state (counterAmountsEntry "guarded") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def counterAmountsContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

private def counterAmountValue (amount : Nat) : List (String × Value) :=
  [ ("owner", .bytes 32 (List.replicate 32 1))
  , ("spender", .bytes 32 (List.replicate 32 2))
  , ("amount", .uint (2 ^ 16 - 1) amount)
  , ("enabled", .bool Bool.true)
  ]

#guard match Entrypoint.run counterAmountsContext (counterAmountsEntry "apply")
    (counterAmountValue (2 ^ 16 - 1))
    {trees := [
      ("total", .scalar (.uint (2 ^ 64 - 1) 10)),
      ("epochs", .map [])
    ]} with
  | .ok (outputs, state) =>
      outputs.lookup "totalValue" == some (.uint (2 ^ 64 - 1) (10 + (2 ^ 16 - 1))) &&
      outputs.lookup "epochValue" == some (.uint (2 ^ 64 - 1) (2 ^ 16 - 1)) &&
      state.trees.lookup "total" == some (.scalar (.uint (2 ^ 64 - 1) (10 + (2 ^ 16 - 1))))
  | .error _ => Bool.false

#guard match Entrypoint.run counterAmountsContext (counterAmountsEntry "apply")
    (counterAmountValue (2 ^ 16))
    {trees := [
      ("total", .scalar (.uint (2 ^ 64 - 1) 0)),
      ("epochs", .map [])
    ]} with
  | .error _ => Bool.true
  | .ok _ => Bool.false

private def counterAmountsUndisclosed : Entrypoint :=
  let operation := counterAmountsEntry "apply"
  {operation with effects := operation.effects.map fun effect =>
    match effect with
    | .counterAdjust state keys subtract _ =>
        .counterAdjust state keys subtract
          (.cast (.uint (2 ^ 32 - 1)) (.ref (ty := .uint (2 ^ 16 - 1)) "amount"))
    | other => other}

#guard match Disclosure.entrypoint counterAmountsUndisclosed with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter 'amount'"
  | .ok _ => Bool.false
