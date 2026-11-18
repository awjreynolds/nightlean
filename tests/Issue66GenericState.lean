import Noctium.Frontend
import Noctium.Backend.Zkir
import Noctium.Verification.GenericStateOps
import Noctium.Verification.GenericStateEncoding
import Noctium.Verification.GenericStateInputValues
import Noctium.Verification.NativeRelationJson

open scoped Noctium
open Noctium Noctium.Verification
open Noctium.Verification.NativeRelation
open Noctium.Verification.NativeState

noctium_circuit issue66Empty where
end

noctium_contract Issue66MixedState where
  cell counter : Native
  cell flag : Bool
  cell quota : UInt 5
  cell untouched : Native
  map claims : UInt 5 => Bool
  map receipts : Native => Native
  entry apply uses issue66Empty where
    read counter as before
    write counter := 2
    read counter as afterWrite
    require eq(afterWrite, 2)
    read quota as available
    require eq(available, 3)
    write quota := uint(4)
    read quota as remaining
    require eq(remaining, 4)
    write flag := true
    read flag as enabled
    require eq(enabled, true)
    absent claims[uint(3)]
    insert claims[uint(3)] := true
    absent receipts[7]
    insert receipts[7] := 11
    read untouched as stable
    require eq(stable, 9)
  end
end

private def issue66Entry : Entrypoint :=
  match Issue66MixedState.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

private def issue66Context : EvalContext :=
  { modulus := Field.modulus,
    poseidon2 := fun _ _ _ => .error "unused by this fixture" }

private def issue66Before : LedgerState := {
  cells := [("counter", .native 0), ("flag", .bool Bool.false),
    ("quota", .uint 31 3), ("untouched", .native 9)],
  maps := [("claims", []), ("receipts", [])]
}

#guard match issue66Entry.run issue66Context [] issue66Before with
  | .ok (outputs, after) =>
    outputs.isEmpty &&
    after.cells.lookup "counter" == some (.native 2) &&
    after.cells.lookup "flag" == some (.bool Bool.true) &&
    after.cells.lookup "quota" == some (.uint 31 4) &&
    after.cells.lookup "untouched" == some (.native 9) &&
    after.maps.lookup "claims" == some [(.uint 31 3, .bool Bool.true)] &&
    after.maps.lookup "receipts" == some [(.native 7, .native 11)]
  | .error _ => Bool.false

#guard match Backend.Impact.lower Issue66MixedState.state issue66Entry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint Issue66MixedState.state issue66Entry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint Issue66MixedState.state issue66Entry with
  | .error _ => Bool.false
  | .ok json =>
    match NativeRelationJson.decode json with
    | .ok _ => Bool.true
    | .error _ => Bool.false

private def issue66Witness (name : String) : Scalar :=
  if name == "%input_afterWrite" then scalar 2 else
  if name == "%input_available" then scalar 3 else
  if name == "%input_remaining" then scalar 4 else
  if name == "%input_enabled" then one else
  if name == "%input_stable" then scalar 9 else zero

private def issue66InitialSlots : List Slot := [
  .cell (field zero), .cell (field zero), .cell (field (scalar 3)),
  .cell (field (scalar 9)), .map [], .map []]

private def issue66FinalSlots : List Slot := [
  .cell (field (scalar 2)), .cell (field one), .cell (field (scalar 4)),
  .cell (field (scalar 9)), .map [(scalar 3, one)],
  .map [(scalar 7, scalar 11)]]

private def issue66ExpectedReads : List Cell := [
  field zero, field (scalar 2), field (scalar 3), field (scalar 4),
  field one, boolean Bool.false, boolean Bool.false, field (scalar 9)]

private def issue66NativeRun (witness : Assignment) :
    Option Machine :=
  match Backend.Impact.lower Issue66MixedState.state issue66Entry with
  | .error _ => none
  | .ok plan =>
    let reads := plan.reads.drop
      ((issue66Entry.circuit.inputs.filter (·.visibility == .«public»)).length)
    let env := GenericStateInputValues.decodeReads reads witness
    match GenericStateOps.evalPlan issue66Context env plan with
    | .error _ => none
    | .ok operations => run operations
        (GenericStateEncoding.initial issue66InitialSlots)

#guard decide (issue66NativeRun issue66Witness =
  some ⟨[.vector issue66FinalSlots], issue66ExpectedReads⟩)

#guard decide (issue66NativeRun (fun name =>
  if name == "%input_afterWrite" then scalar 8 else issue66Witness name) = none)

private def issue66GuardsHold (witness : Assignment) : _root_.Bool :=
  match Backend.Impact.lower Issue66MixedState.state issue66Entry with
  | .error _ => Bool.false
  | .ok plan =>
    let reads := plan.reads.drop
      ((issue66Entry.circuit.inputs.filter (·.visibility == .«public»)).length)
    let env := GenericStateInputValues.decodeReads reads witness
    plan.guards.all fun guard =>
      match guard.eval issue66Context env with
      | .ok Bool.true => Bool.true
      | _ => Bool.false

#guard issue66GuardsHold issue66Witness
#guard decide (issue66NativeRun (fun name =>
  if name.startsWith "%input__noctium_absence_" then one
  else issue66Witness name) =
    some ⟨[.vector issue66FinalSlots], issue66ExpectedReads⟩)
#guard !issue66GuardsHold (fun name =>
  if name.startsWith "%input__noctium_absence_" then one
  else issue66Witness name)

private def issue66NativeRunMutated (change : List Op → List Op) :
    Option Machine :=
  match Backend.Impact.lower Issue66MixedState.state issue66Entry with
  | .error _ => none
  | .ok plan =>
    let reads := plan.reads.drop
      ((issue66Entry.circuit.inputs.filter (·.visibility == .«public»)).length)
    let env := GenericStateInputValues.decodeReads reads issue66Witness
    match GenericStateOps.evalPlan issue66Context env plan with
    | .error _ => none
    | .ok operations => run (change operations)
        (GenericStateEncoding.initial issue66InitialSlots)

private def issue66ExpectedMachine : Option Machine :=
  some ⟨[.vector issue66FinalSlots], issue66ExpectedReads⟩

#guard decide (issue66NativeRunMutated (fun operations =>
  operations.map fun operation =>
    if operation == Op.index 4 Bool.true then Op.index 5 Bool.true
    else operation) != issue66ExpectedMachine)

#guard decide (issue66NativeRunMutated (fun operations =>
  operations.map fun operation =>
    if operation == Op.push (field (scalar 3)) Bool.false then
      Op.push (field (scalar 4)) Bool.false else operation) != issue66ExpectedMachine)

#guard decide (issue66NativeRunMutated (fun operations =>
  operations.map fun operation =>
    if operation == Op.push (field (scalar 11)) Bool.true then
      Op.push (field (scalar 12)) Bool.true else operation) != issue66ExpectedMachine)

#guard decide (issue66NativeRunMutated List.reverse != issue66ExpectedMachine)
