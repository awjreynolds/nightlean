import Nightlean.Backend.Impact
import Nightlean.Backend.Zkir
import Nightlean.Frontend

open scoped Nightlean
open Nightlean

nightlean_circuit issue68MapRead where
  public account : Native
end

nightlean_contract Issue68MapReads where
  map balances : Native => Native
  entry update uses issue68MapRead where
    insert balances[account] := 7
    read balances[account] as previous
    insert balances[account] := add(previous, 1)
    read balances[account] as updated
    require eq(updated, 8)
  end
end

private def issue68Entry : Entrypoint :=
  match Issue68MapReads.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

private def issue68Context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

#guard match Entrypoint.run issue68Context issue68Entry [("account", .native 17)] {
  maps := [("balances", [])]
} with
  | .ok (outputs, state) => outputs.isEmpty &&
      state.maps.lookup "balances" == some [(.native 17, .native 8)]
  | .error _ => Bool.false

#guard match Backend.Impact.lower Issue68MapReads.state issue68Entry with
  | .ok plan => plan.operations.any fun operation =>
      match operation with | .mapIndex _ _ => Bool.true | _ => Bool.false
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint Issue68MapReads.state issue68Entry with
  | .ok _ => Bool.true
  | .error _ => Bool.false
