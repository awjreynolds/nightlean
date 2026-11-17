import Nightlean.Backend.Zkir
import Nightlean.Frontend

open scoped Nightlean
open Nightlean

nightlean_circuit emptyCircuit where
end

nightlean_contract OrderedState where
  cell counter : Native
  cell untouched : Native
  cell flag : Bool
  cell amount : UInt 8
  map spent : Native => Bool
  entry sequential uses emptyCircuit where
    read counter as initial
    write counter := 1
    read counter as afterFirst
    write counter := 2
    read counter as afterSecond
    read untouched as stableAfterWrites
    write flag := true
    read flag as flagAfter
    write amount := uint(255)
    read amount as amountAfter
    insert spent[0] := true
    read untouched as stableAfterMapInsert
    require eq(afterFirst, 1)
    require eq(afterSecond, 2)
    require eq(stableAfterWrites, 9)
    require eq(flagAfter, true)
    require eq(amountAfter, 255)
    require eq(stableAfterMapInsert, 9)
  end
  entry failingGuard uses emptyCircuit where
    write counter := 1
    read counter as observed
    require eq(observed, 2)
  end
  entry noncanonicalRead uses emptyCircuit where
    write counter := 1
    read flag as observedFlag
    require eq(observedFlag, false)
  end
end

private def sequentialEntry : Entrypoint :=
  match OrderedState.entrypoints with
  | ep :: _ => ep
  | _ => { name := "missing", circuit := { name := "missing" } }

private def sourceContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
}

#guard match Entrypoint.run sourceContext sequentialEntry [] {
  cells := [
    ("counter", .native 0),
    ("untouched", .native 9),
    ("flag", .bool Bool.false),
    ("amount", .uint 255 0)
  ],
  maps := [("spent", [])]
} with
  | .ok (_, after) =>
    after.cells.lookup "counter" == some (.native 2) &&
    after.cells.lookup "untouched" == some (.native 9) &&
    after.cells.lookup "flag" == some (.bool Bool.true) &&
    after.cells.lookup "amount" == some (.uint 255 255) &&
    after.maps.lookup "spent" == some [(.native 0, .bool Bool.true)]
  | .error _ => Bool.false

#guard match Backend.Impact.lower OrderedState.state sequentialEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint OrderedState.state sequentialEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match (match OrderedState.entrypoints with
  | _ :: ep :: _ => Entrypoint.run sourceContext ep [] {
      cells := [("counter", .native 0)], maps := [("spent", [])]
    }
  | _ => .error "missing failing-guard entry") with
  | .error _ => Bool.true
  | .ok _ => Bool.false
