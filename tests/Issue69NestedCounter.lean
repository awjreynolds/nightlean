import Nightlean.Backend.Impact
import Nightlean.Backend.Zkir
import Nightlean.Frontend

open scoped Nightlean
open Nightlean

nightlean_circuit issue69NestedCounter where
  private owner : Bytes32
  private spender : Bytes32
end

nightlean_contract Issue69NestedCounter where
  tree epochs : Bytes32 => Bytes32 => UInt 64
  entry bump uses issue69NestedCounter where
    member epochs[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert epochs[disclose(owner)] := emptyMap
    } else {
    }
    member epochs[disclose(owner)][disclose(spender)] as spenderPresent
    if eq(spenderPresent, false) then {
      insert epochs[disclose(owner)][disclose(spender)] := uint(0)
    } else {
    }
    read epochs[disclose(owner)][disclose(spender)] as current
    write epochs[disclose(owner)][disclose(spender)] := cast(UInt 64, add(current, uint(1)))
    read epochs[disclose(owner)][disclose(spender)] as updated
    require eq(updated, add(current, uint(1)))
  end
end

private def issue69NestedEntry : Entrypoint :=
  match Issue69NestedCounter.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Impact.lower Issue69NestedCounter.state issue69NestedEntry with
  | .ok plan =>
      plan.reads.any (·.name == "ownerPresent") &&
      plan.reads.any (·.name == "spenderPresent") &&
      plan.reads.any (·.name == "current") &&
      plan.reads.any (·.name == "updated") &&
      plan.operations.any (fun op => match op with | .newMap => Bool.true | _ => Bool.false)
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint Issue69NestedCounter.state issue69NestedEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def issue69EvalContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

private def issue69ZeroKey : Value := .bytes 32 (List.replicate 32 0)
private def issue69ExpectedTree : LedgerValue := .map [
  (issue69ZeroKey, .map [(issue69ZeroKey, .scalar (.uint (2 ^ 64 - 1) 1))])]

#guard match Entrypoint.run issue69EvalContext issue69NestedEntry
    [("owner", issue69ZeroKey), ("spender", issue69ZeroKey)]
    {trees := [("epochs", .map [])]} with
  | .ok (outputs, state) => outputs.isEmpty &&
      state.trees.lookup "epochs" == some issue69ExpectedTree
  | .error _ => Bool.false

private def issue69HiddenPathEntry : Entrypoint := {
  name := "hiddenPath"
  circuit := {
    name := "hiddenPath"
    inputs := [{name := "owner", ty := .bytes 32, visibility := .private}]
  }
  effects := [.memberPath "epochs" "exists" [
    .mk (.bytes 32) (.ref (ty := .bytes 32) "owner")]]
}

#guard match Disclosure.entrypoint issue69HiddenPathEntry with
  | .error diagnostic => diagnostic.message.contains "undisclosed private parameter 'owner'"
  | .ok _ => Bool.false
