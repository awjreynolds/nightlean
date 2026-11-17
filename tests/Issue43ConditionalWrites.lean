import Nightlean.Backend.Impact
import Nightlean.Backend.Zkir
import Nightlean.Frontend

open scoped Nightlean
open Nightlean

nightlean_circuit issue43ConditionalWrites where
  private enabled : Bool
  public account : Native
end

nightlean_contract Issue43ConditionalWrites where
  cell current : Native
  map allowances : Native => Native
  entry apply uses issue43ConditionalWrites where
    when disclose(enabled) write current := 21
    when disclose(enabled) insert allowances[account] := 9
  end
end

private def issue43Entry : Entrypoint :=
  match Issue43ConditionalWrites.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

private def issue43Context : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

private def issue43Inputs (enabled : _root_.Bool) : EvalEnv := [
  ("enabled", .bool enabled), ("account", .native 7)]

private def issue43Initial : LedgerState := {
  cells := [("current", .native 4)]
  maps := [("allowances", [])]
}

#guard match issue43Entry.run issue43Context (issue43Inputs Bool.true) issue43Initial with
  | .ok (outputs, after) => outputs.isEmpty &&
      after.cells.lookup "current" == some (.native 21) &&
      after.maps.lookup "allowances" == some [(.native 7, .native 9)]
  | .error _ => Bool.false

#guard match issue43Entry.run issue43Context (issue43Inputs Bool.false) issue43Initial with
  | .ok (outputs, after) => outputs.isEmpty && after == issue43Initial
  | .error _ => Bool.false

private def issue43Undisclosed : Entrypoint :=
  {issue43Entry with effectGuards := [
    some (.ref "enabled" : Expr .bool),
    some (.disclose {} (.ref "enabled" : Expr .bool))]}

#guard match Disclosure.entrypoint issue43Undisclosed with
  | .error _ => Bool.true
  | .ok _ => Bool.false

private def issue43Partial : Entrypoint :=
  {issue43Entry with
    effects := [.writeCell "current" .native
      (.cast .native (.usub (.uint 3 1) (.uint 3 2)))]
    effectGuards := [some (.disclose {} (.ref "enabled" : Expr .bool))]}

#guard match issue43Partial.validate
    {poseidon2 := Bool.true, stateCells := Bool.true, stateMaps := Bool.true}
    Issue43ConditionalWrites.state with
  | .error diagnostic => diagnostic.message.startsWith "guarded write payload contains a partial expression"
  | .ok _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint
    Issue43ConditionalWrites.state issue43Entry with
  | .ok _ => Bool.true
  | .error _ => Bool.false
