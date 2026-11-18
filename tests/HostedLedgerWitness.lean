import Noctium.Frontend

open Noctium Noctium.Helpers

private def lookupWitness : List WitnessSignature := [{
  name := "lookup"
  operation := "noctium.lookup.v1"
  capability := "lookup"
  parameters := [{name := "balance", type := .scalar .native}]
  result := .scalar .native}]

private def hostedCellProgram : Program := {
  witnesses := lookupWitness
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    result := .unit
    body := [
      .readCell "balance" "before" .native,
      .bind "next" (.scalar .native) (.witnessCall "lookup" "lookup" [.ref "before"]),
      .writeCell "balance" .native (.disclose {} (.ref "next")),
      .return none]}]
  exports := [{name := "update", target := ⟨0, 0⟩}]}

private def guardedCellProgram : Program := {
  witnesses := lookupWitness
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    parameters := [⟨"enabled", .bool⟩]
    result := .unit
    body := [
      .readCell "balance" "before" .native,
      .branch (.ref "enabled") [
        .evaluate (.witnessCall "lookup" "lookup" [.ref "before"])] [],
      .return none]}]
  exports := [{name := "update", target := ⟨0, 0⟩, inputs := [
    {name := "enabled", ty := .bool, visibility := .public}]}]}

private def cellSchema : List StateDecl := [{name := "balance", kind := .cell .native}]

#guard match Helpers.compileHostedEntrypointForWithLimits {} hostedCellProgram "update" cellSchema with
  | .ok {entrypoint, calls := [call]} =>
    (match entrypoint.effects.take call.effectCount, entrypoint.effects.drop call.effectCount with
      | [.readCell "balance" _ .native], [.writeCell "balance" .native _] => _root_.Bool.true
      | _, _ => _root_.Bool.false) &&
      entrypoint.circuit.inputs.any (·.name == call.inputs.headD "")
  | _ => _root_.Bool.false

#guard match Helpers.compileHostedEntrypointForWithLimits {} guardedCellProgram "update" cellSchema with
  | .ok {entrypoint, calls := [call]} =>
    call.guarded && call.effectCount > 0 && !entrypoint.circuit.constraints.isEmpty
  | _ => _root_.Bool.false

#guard !(Helpers.compileEntrypointForWithLimits {} hostedCellProgram "update" cellSchema).isOk

private def undisclosedProgram : Program := {
  hostedCellProgram with declarations := hostedCellProgram.declarations.map fun declaration =>
    {declaration with body := [
      .readCell "balance" "before" .native,
      .bind "next" (.scalar .native) (.witnessCall "lookup" "lookup" [.ref "before"]),
      .writeCell "balance" .native (.ref "next"),
      .return none]}}

#guard !(Helpers.compileHostedEntrypointForWithLimits {} undisclosedProgram "update" cellSchema).isOk
