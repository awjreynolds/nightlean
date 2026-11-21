import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit optionalListHeadInput where
  private owner : Bytes32
  private spender : Bytes32
  private x : Native
  private y : Native
  public enabled : Bool
end

noctium_contract OptionalListHead where
  list inbox : struct Memo {
    local_0 : Native
    y : Native
  }
  tree records : Bytes32 => Bytes32 => List struct Memo {
    local_0 : Native
    y : Native
  }
  entry seed uses optionalListHeadInput where
    member records[disclose(owner)] as ownerPresent
    if eq(ownerPresent, false) then {
      insert records[disclose(owner)] := emptyMap
    } else {
    }
    member records[disclose(owner)][disclose(spender)] as recordPresent
    if eq(recordPresent, false) then {
      reset records[disclose(owner)][disclose(spender)]
    } else {
    }
    pushFront inbox := fields(disclose(x), disclose(y))
    pushFront records[disclose(owner)][disclose(spender)] := fields(disclose(x), disclose(y))
  end
  entry inspectInbox uses optionalListHeadInput where
    -- Guard the generated length binding against implicit record-field names.
    headOrDefault inbox as (inboxPresent, noctium_if)
    return present : Bool := inboxPresent
    return first : Native := noctium_if_local_0
    return second : Native := noctium_if_y
  end
  entry inspectPath uses optionalListHeadInput where
    headOrDefault records[disclose(owner)][disclose(spender)] as (recordPresent, recordHead)
    return present : Bool := recordPresent
    return first : Native := recordHead_local_0
    return second : Native := recordHead_y
  end
  entry inspectGuarded uses optionalListHeadInput where
    when enabled headOrDefault records[disclose(owner)][disclose(spender)] as (recordPresent, noctium_if)
    return present : Bool := recordPresent
    return first : Native := noctium_if_local_0
    return second : Native := noctium_if_y
  end
end

private def optionalListHeadEntry (name : String) : Noctium.Entrypoint :=
  match OptionalListHead.entrypoints.find? (·.name == name) with
  | some found => found
  | none => {name := "missing", circuit := {name := "missing"}}

private def optionalListHeadContext : Noctium.EvalContext := {
  modulus := Noctium.Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

#guard
  match Noctium.Entrypoint.run optionalListHeadContext
      (optionalListHeadEntry "inspectInbox")
      [("owner", .bytes 32 (List.replicate 32 1)),
       ("spender", .bytes 32 (List.replicate 32 2)),
       ("x", .native 0), ("y", .native 0), ("enabled", .bool Bool.true)]
      {trees := [("inbox", .list []), ("records", .map [])]} with
  | .ok (outputs, _) =>
      outputs.lookup "present" == some (.bool Bool.false) &&
      outputs.lookup "first" == some (.native 0) &&
      outputs.lookup "second" == some (.native 0)
  | .error _ => Bool.false

private def optionalListHeadInputs : List (String × Noctium.Value) :=
  [("owner", .bytes 32 (List.replicate 32 1)),
   ("spender", .bytes 32 (List.replicate 32 2)),
   ("x", .native 0), ("y", .native 0), ("enabled", .bool Bool.true)]

#guard
  let empty : Noctium.LedgerState :=
    {trees := [("inbox", .list []), ("records", .map [])]}
  match Noctium.Entrypoint.run optionalListHeadContext
      (optionalListHeadEntry "seed") optionalListHeadInputs empty with
  | .ok (_, seeded) =>
      match Noctium.Entrypoint.run optionalListHeadContext
          (optionalListHeadEntry "inspectPath") optionalListHeadInputs seeded with
      | .ok (outputs, _) =>
          outputs.lookup "present" == some (.bool Bool.true) &&
          outputs.lookup "first" == some (.native 0) &&
          outputs.lookup "second" == some (.native 0)
      | .error _ => Bool.false
  | .error _ => Bool.false

#guard match Noctium.Backend.Impact.lower OptionalListHead.state
    (optionalListHeadEntry "inspectPath") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Noctium.Backend.Zkir.lowerEntrypoint OptionalListHead.state
    (optionalListHeadEntry "inspectGuarded") with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Noctium.Disclosure.entrypoint (optionalListHeadEntry "inspectPath") with
  | .ok _ => Bool.true
  | .error _ => Bool.false
