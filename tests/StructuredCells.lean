import Noctium.Frontend

open scoped Noctium
open Noctium Noctium.Helpers

def structuredCellProgram : Program := {
  ledger := [{name := "balance", kind := .cell .native}]
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    parameters := [⟨"enabled", .bool⟩, ⟨"amount", .native⟩]
    result := .scalar .native
    body := [
      .branch (.disclose {} (.ref "enabled")) [
        .bind "checkedAmount" (.scalar (.uint 7)) (.cast (.uint 7) (.ref "amount")),
        .readCell "balance" "before" .native,
        .writeCell "balance" .native (.binary .add (.ref "before") (.ref "amount"))] [],
      .readCell "balance" "after" .native,
      .return (some (.ref "after"))] }]
  exports := [{name := "update", target := ⟨0, 0⟩, inputs := [
    {name := "enabled", ty := .bool, visibility := .private},
    {name := "amount", ty := .native, visibility := .public}]}]
}

noctium_contract StructuredCells where
  cell balance : Native
  entry update from structuredCellProgram entry "update" end
end

private def structuredCellEntry : Entrypoint :=
  match StructuredCells.entrypoints with
  | compiledEntry :: _ => compiledEntry
  | [] => {name := "missing", circuit := {name := "missing"}}

#guard !(Helpers.compile structuredCellProgram "update").isOk
#guard (Helpers.compileEntrypointFor structuredCellProgram "update" StructuredCells.state).isOk
#guard (structuredCellEntry.validate Capabilities.source StructuredCells.state).isOk

private def undisclosedCellWrite : Program := {
  ledger := structuredCellProgram.ledger
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    parameters := [⟨"enabled", .bool⟩]
    result := .unit
    body := [.branch (.ref "enabled")
      [.writeCell "balance" .native (.native 1)] []]}]
  exports := [{name := "update", target := ⟨0, 0⟩, inputs := [
    {name := "enabled", ty := .bool, visibility := .private}]}]
}

#guard !(Helpers.compileEntrypointFor undisclosedCellWrite "update" StructuredCells.state).isOk

private def wrongCellRead : Program := {
  ledger := structuredCellProgram.ledger
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    result := .scalar .bool
    body := [
      .readCell "balance" "wrong" .bool,
      .return (some (.ref "wrong"))]}]
  exports := [{name := "update", target := ⟨0, 0⟩}]
}

#guard !(Helpers.compileEntrypointFor wrongCellRead "update" StructuredCells.state).isOk

#guard !(Helpers.compileEntrypointFor structuredCellProgram "update"
  [{name := "balance", kind := .cell .native, «sealed» := Bool.true}]).isOk

private def unitFailureRetained (statement : Statement) : _root_.Bool :=
  let program : Program := {
    declarations := [{
      id := ⟨0, 0⟩
      name := "main"
      result := .unit
      body := [statement, .return none]}]
    exports := [{name := "main", target := ⟨0, 0⟩}]}
  match Helpers.compileEntrypoint program "main" with
  | .error _ => Bool.false
  | .ok compiledEntry => !(compiledEntry.run {
      modulus := Field.modulus
      poseidon2 := fun _ _ _ => .error "unused"} [] {}).isOk

-- A Unit return must not erase strict failures in discarded values or unused lets.
#guard unitFailureRetained (.evaluate (.cast (.uint 0) (.native 1)))
#guard unitFailureRetained (.bind "unused" (.scalar (.uint 0)) (.cast (.uint 0) (.native 1)))
