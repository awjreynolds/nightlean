import Nightlean.Backend.Impact
import Nightlean.Backend.NativeExpected
import Nightlean.Backend.Zkir
import Nightlean.Frontend

open scoped Nightlean
open Lean Nightlean

nightlean_circuit issue43GuardedReads where
  public account : Native
  public enabled : Bool
end

nightlean_contract Issue43GuardedReads where
  cell marker : Native
  map balances : Native => Native
  entry update uses issue43GuardedReads where
    member balances[account] as existed
    when existed read marker as skippedCell
    when existed read balances[account] as missingValue
    when eq(existed, false) insert balances[account] := 99
    when eq(existed, false) member balances[account] as initialized
    when initialized read balances[account] as currentValue
    when enabled read marker as markerValue
  end
end

private def issue43GuardedEntry : Entrypoint :=
  match Issue43GuardedReads.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

private def issue43GuardedInputs : EvalEnv := [
  ("account", .native 7), ("enabled", .bool Bool.true)]

private def issue43GuardedState : LedgerState := {
  cells := [("marker", .native 23)]
  maps := [("balances", [])]
}

private def issue43GuardedContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

#guard match issue43GuardedEntry.run issue43GuardedContext issue43GuardedInputs issue43GuardedState with
  | .ok (outputs, after) => outputs.isEmpty &&
      after.cells.lookup "marker" == some (.native 23) &&
      after.maps.lookup "balances" == some [(.native 7, .native 99)]
  | .error _ => Bool.false

private def replaceJsonField (value : Json) (name : String) (replacement : Json) : Json :=
  match value.getObj? with
  | .error _ => value
  | .ok object => Json.mkObj ((object.toList.filter (·.1 != name)) ++ [(name, replacement)])

private def guardedReadMutationRejected (change : List Json → List Json) : _root_.Bool :=
  match Backend.Native.expectedEntrypoint Issue43GuardedReads.state issue43GuardedEntry,
      Backend.Zkir.lowerEntrypoint Issue43GuardedReads.state issue43GuardedEntry with
  | .ok expected, .ok program =>
    let instructions := (program.getObjValD "instructions").getArr?.toOption.getD #[]
    let changed := replaceJsonField program "instructions" (toJson (change instructions.toList))
    !(Backend.Native.validate expected changed).isOk
  | _, _ => Bool.false

private def removeFirstAssert : List Json → List Json
  | [] => []
  | instruction :: rest =>
    if (instruction.getObjValD "op").getStr?.toOption == some "assert" then rest
    else instruction :: removeFirstAssert rest

#guard guardedReadMutationRejected (fun instructions => instructions.map fun instruction =>
  if (instruction.getObjValD "op").getStr?.toOption == some "public_input" &&
      (instruction.getObjValD "output").getStr?.toOption == some "%input_skippedCell" then
    replaceJsonField instruction "guard" Json.null
  else instruction)

#guard guardedReadMutationRejected removeFirstAssert
