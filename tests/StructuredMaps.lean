import Noctium.Frontend

open scoped Noctium
open Noctium Noctium.Helpers

def structuredMapProgram : Program := {
  ledger := [{name := "balances", kind := .map (.bytes 32) .native}]
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    parameters := [⟨"enabled", .bool⟩, ⟨"account", .bytes 32⟩, ⟨"amount", .native⟩]
    result := .scalar .native
    body := [
      .bind "key" (.scalar (.bytes 32)) (.ref "account"),
      .branch (.disclose {} (.ref "enabled")) [
        .bind "checkedAmount" (.scalar (.uint 7)) (.cast (.uint 7) (.ref "amount")),
        .readMember "balances" "wasPresent" (.bytes 32) .native (.ref "key"),
        .branch (.ref "wasPresent") [
          .readMap "balances" "old" (.bytes 32) .native (.ref "key"),
          .writeMap "balances" (.bytes 32) .native (.ref "key")
            (.binary .add (.ref "old") (.ref "amount"))] [
          .writeMap "balances" (.bytes 32) .native (.ref "key") (.ref "amount")]] [],
      .readMember "balances" "present" (.bytes 32) .native (.ref "key"),
      .branch (.ref "present") [
        .readMap "balances" "current" (.bytes 32) .native (.ref "key"),
        .return (some (.ref "current"))] [
        .return (some (.native 0))]] }]
  exports := [{name := "update", target := ⟨0, 0⟩, inputs := [
    {name := "enabled", ty := .bool, visibility := .private},
    {name := "account", ty := .bytes 32, visibility := .public},
    {name := "amount", ty := .native, visibility := .public}]}]
}

noctium_contract StructuredMaps where
  map balances : Bytes32 => Native
  entry update from structuredMapProgram entry "update" end
end

#guard !(Helpers.compile structuredMapProgram "update").isOk
#guard (Helpers.compileEntrypointFor structuredMapProgram "update" StructuredMaps.state).isOk

private def undisclosedMapKey : Program := {
  structuredMapProgram with
    declarations := [{
      id := ⟨0, 0⟩, name := "write", result := .unit
      parameters := [⟨"account", .bytes 32⟩]
      body := [
        .writeMap "balances" (.bytes 32) .native (.ref "account") (.native 1),
        .return none]}]
    exports := [{name := "write", target := ⟨0, 0⟩, inputs := [
      {name := "account", ty := .bytes 32, visibility := .private}]}]
}

#guard !(Helpers.compileEntrypointFor undisclosedMapKey "write" StructuredMaps.state).isOk

private def wrongMapKeyType : Program := {
  structuredMapProgram with
    declarations := [{
      id := ⟨0, 0⟩, name := "update", result := .scalar .bool
      body := [
        .readMember "balances" "present" .native .native (.native 1),
        .return (some (.ref "present"))]}]
    exports := [{name := "update", target := ⟨0, 0⟩}]
}

#guard !(Helpers.compileEntrypointFor wrongMapKeyType "update" StructuredMaps.state).isOk
