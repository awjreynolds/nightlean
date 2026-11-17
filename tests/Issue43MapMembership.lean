import Nightlean.Backend.Impact
import Nightlean.Backend.Zkir
import Nightlean.Frontend

open scoped Nightlean
open Nightlean

nightlean_circuit issue43MapMembership where
  public account : Native
  public proposed : Native
end

nightlean_contract Issue43MapMembership where
  map balances : Native => Native
  entry initOnce uses issue43MapMembership where
    insert balances[8] := 99
    member balances[account] as present
    when disclose(eq(present, false)) insert balances[account] := proposed
  end
end

private def issue43MembershipEntry : Entrypoint :=
  match Issue43MapMembership.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

private def issue43MembershipContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

private def issue43MembershipInputs (proposed : Nat) : EvalEnv := [
  ("account", .native 7), ("proposed", .native proposed)]

private def issue43MembershipEmpty : LedgerState := {
  maps := [("balances", [])]
}

#guard match issue43MembershipEntry.run issue43MembershipContext
    (issue43MembershipInputs 13) issue43MembershipEmpty with
  | .ok (outputs, after) => outputs.isEmpty &&
      after.maps.lookup "balances" == some [
        (.native 7, .native 13), (.native 8, .native 99)]
  | .error _ => Bool.false

#guard match issue43MembershipEntry.run issue43MembershipContext
    (issue43MembershipInputs 17)
    {issue43MembershipEmpty with maps := [("balances", [(.native 7, .native 13)])]} with
  | .ok (outputs, after) => outputs.isEmpty &&
      after.maps.lookup "balances" == some [
        (.native 8, .native 99), (.native 7, .native 13)]
  | .error _ => Bool.false

#guard match Backend.Impact.lower Issue43MapMembership.state issue43MembershipEntry with
  | .ok plan => plan.reads.map (·.ty) == [.native, .native, .bool] &&
      plan.operations.length == 17
  | .error _ => Bool.false
