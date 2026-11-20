import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit callerInputs where
  public enabled : Bool
end

noctium_contract NativeCaller where
  cell recorded : Bool
  entry lookup uses callerInputs where
    when enabled readCaller as (present, isContract, contractId, userId)
    when enabled write recorded := present
    return hasCaller : Bool := present
    return contractCaller : Bool := isContract
    return callerContract : Bytes32 := contractId
    return callerUser : Bytes32 := userId
  end
end

#guard
  let ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
  let bytes := List.range 32
  let zero := List.replicate 32 0
  match NativeCaller.entrypoints with
  | [ep] =>
    [(Bool.true, some (.contract bytes), Bool.true, Bool.true, bytes, zero, Bool.false, Bool.true),
      (Bool.true, some (.user bytes), Bool.true, Bool.false, zero, bytes, Bool.false, Bool.true),
      (Bool.true, none, Bool.false, Bool.false, zero, zero, Bool.true, Bool.false),
      (Bool.false, some (.contract bytes), Bool.false, Bool.false, zero, zero, Bool.true, Bool.true)].all
      fun (enabled, caller, present, isContract, contractId, userId, initialRecorded, expectedRecorded) =>
        match ep.run {ctx with caller} [("enabled", .bool enabled)]
            {cells := [("recorded", .bool initialRecorded)]} with
        | .ok (outputs, state) => outputs == [
            ("hasCaller", .bool present), ("contractCaller", .bool isContract),
            ("callerContract", .bytes 32 contractId), ("callerUser", .bytes 32 userId)] &&
            state.cells == [("recorded", .bool expectedRecorded)]
        | .error _ => Bool.false
  | _ => Bool.false

#guard
  let ep : Entrypoint := {
    name := "guardedCaller",
    circuit := {name := "guardedCaller", inputs := [{name := "secret", ty := .bool, visibility := .private}]},
    effects := [.readCaller {present := "p", isContract := "c", contractAddress := "contract", userAddress := "user"}],
    effectGuards := [some (.ref "secret")]
  }
  match Disclosure.entrypoint ep with
  | .error diagnostic => diagnostic.message.contains "reaches public caller read guard"
  | .ok _ => Bool.false
