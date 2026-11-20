import Noctium.Frontend

open scoped Noctium

noctium_circuit addressInputs where
  public enabled : Bool
end

noctium_contract NativeContractAddress where
  cell lastAddress : Bytes32
  entry identify uses addressInputs where
    when enabled readSelf as own
    when enabled write lastAddress := own
    return address : Bytes32 := own
  end
end

open Noctium

#guard
  let bytes := List.range 32
  let zero := List.replicate 32 0
  let ctx : EvalContext := {
    modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused",
    ownContractAddress := some bytes, contractCaller := some (List.replicate 32 99)
  }
  let initial : LedgerState := {cells := [("lastAddress", .bytes 32 zero)]}
  match NativeContractAddress.entrypoints with
  | [ep] =>
    let enabled := [("enabled", Value.bool Bool.true)]
    let disabled := [("enabled", Value.bool Bool.false)]
    let missing := {ctx with ownContractAddress := none}
    let malformed := {ctx with ownContractAddress := some (List.replicate 32 256)}
    match ep.run ctx enabled initial, ep.run missing disabled initial,
        ep.run missing enabled initial, ep.run malformed enabled initial with
    | .ok (active, activeState), .ok (inactive, inactiveState),
        .error missingMessage, .error malformedMessage =>
      active == [("address", .bytes 32 bytes)] &&
        activeState.cells == [("lastAddress", .bytes 32 bytes)] &&
        inactive == [("address", .bytes 32 zero)] && inactiveState == initial &&
        missingMessage == "missing execution contract address" &&
        malformedMessage == "invalid execution contract address"
    | _, _, _, _ => Bool.false
  | _ => Bool.false

#guard
  let subject : Entrypoint := {
    name := "privateGuard"
    circuit := {name := "privateGuard", inputs := [{name := "enabled", ty := .bool, visibility := .private}]}
    effects := [.readContractAddress "own"]
    effectGuards := [some (.ref "enabled")]
  }
  match Disclosure.entrypoint subject with
  | .error diagnostic => diagnostic.message.contains "undisclosed private control from parameter 'enabled'"
  | .ok _ => Bool.false
