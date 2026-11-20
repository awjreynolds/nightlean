import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit checkpointInputs where
  public enabled : Bool
end

noctium_contract NativeCheckpoint where
  cell firstMark : Native
  cell secondMark : Native
  entry apply uses checkpointInputs where
    write firstMark := 1
    when enabled checkpoint
    write secondMark := 2
    read secondMark as result
    return current : Native := result
  end
end

#guard
  let context : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
  let state : LedgerState := {cells := [("firstMark", .native 0), ("secondMark", .native 0)]}
  match NativeCheckpoint.entrypoints with
  | [ep] =>
    [Bool.true, Bool.false].all fun enabled =>
      match ep.run context [("enabled", .bool enabled)] state with
      | .ok (outputs, after) => outputs == [("current", .native 2)] &&
          after.cells.lookup "firstMark" == some (.native 1) &&
          after.cells.lookup "secondMark" == some (.native 2)
      | .error _ => Bool.false
  | _ => Bool.false

#guard
  let privateGuard : Entrypoint := {
    name := "privateCheckpoint",
    circuit := {name := "privateCheckpoint", inputs := [{name := "flag", ty := .bool, visibility := .private}]},
    effects := [.checkpoint],
    effectGuards := [some (.ref "flag")]
  }
  match Disclosure.entrypoint privateGuard with
  | .error diagnostic => diagnostic.message.contains "reaches public ledger checkpoint"
  | .ok _ => Bool.false
