import Noctium.Frontend

open scoped Noctium
open Noctium Noctium.Helpers

private def iterationSource : Except Diagnostic Program := do
  let vector := Types.CompositeType.vector 3 (.scalar .native)
  let item := Types.CompositeType.structure "Iteration.Item"
  let base : Program := {
    composites := {structures := [{id := "Iteration.Item", fields := [
      {name := "amount", type := .scalar .native},
      {name := "metadata", type := .vector 2 (.scalar .native)}]}]}
    ledger := [{name := "total", kind := .cell .native}]
    witnesses := [
      {name := "seed", operation := "noctium.iteration-seed.v1", capability := "seed",
        result := .scalar .native},
      {name := "values", operation := "noctium.iteration-values.v1", capability := "values",
        result := .composite vector},
      {name := "double", operation := "noctium.iteration-double.v1", capability := "double",
        parameters := [{name := "value", type := .scalar .native}], result := .scalar .native}]
    declarations := [{
      id := ⟨0, 0⟩, name := "update",
      parameters := [⟨"enabled", .bool⟩, ⟨"expected", .native⟩, ⟨"offset", .native⟩],
      result := .scalar .native, body := [.return (some (.native 0))]}]
    exports := [{name := "update", target := ⟨0, 0⟩, inputs := [
      {name := "enabled", ty := .bool, visibility := .private},
      {name := "expected", ty := .native, visibility := .public},
      {name := "offset", ty := .native, visibility := .private}]}]
  }
  let env : Environment := [
    ("enabled", .scalar .bool), ("expected", .scalar .native), ("offset", .scalar .native)]
  let (mappedProgram, mapped) ← Iteration.mapWithLimits {} base 0 env {}
    [.witnessCall "input-values" "values" []]
    (.anonymous [{name := "value"}] none [
      .bind "shifted" (.scalar .native) (.binary .add (.ref "value") (.ref "offset")),
      .bind "doubled" (.scalar .native) (.witnessCall "double-value" "double" [.ref "shifted"]),
      .return (some (.composite item [.ref "doubled", .ref "shifted", .ref "value"]))])
  let (foldedProgram, folded) ← Iteration.foldWithLimits {} mappedProgram 0 env {}
    (.witnessCall "initial-seed" "seed" []) mapped
    (.anonymous [{name := "acc"}, {name := "value"}] none [
      .return (some (.binary .add (.ref "acc") (.project (.ref "value") (.field "amount"))))])
  pure {foldedProgram with declarations := foldedProgram.declarations.map fun declaration =>
    if declaration.id == ⟨0, 0⟩ then {declaration with body := [
      .branch (.disclose {} (.ref "enabled")) [
        .bind "sum" (.scalar .native) folded,
        .assert (.eq (.ref "sum") (.ref "expected")),
        .writeCell "total" .native (.disclose {} (.ref "sum")),
        .stage "private" "iteration/last" .native (.ref "sum")] [],
      .readCell "total" "after" .native,
      .return (some (.ref "after"))]}
    else declaration}

#guard iterationSource.isOk

private def iterationProgram : Program :=
  match iterationSource with
  | .ok program => program
  | .error _ => {}

noctium_contract IterationWitness where
  cell total : Native
  entry update from iterationProgram entry "update" end
end

private def withoutWriteReleases : List Statement → List Statement
  | [] => []
  | .writeCell state ty (.disclose _ value) :: rest =>
    .writeCell state ty value :: withoutWriteReleases rest
  | .branch condition yes no :: rest =>
    .branch condition (withoutWriteReleases yes) (withoutWriteReleases no) :: withoutWriteReleases rest
  | statement :: rest => statement :: withoutWriteReleases rest
termination_by body => sizeOf body

#guard match Witness.compileStateEntrypoint
    (Helpers.mapDeclarationBodies withoutWriteReleases iterationProgram) "update" iterationProgram.ledger with
  | .error diagnostic => (diagnostic.message.splitOn "private").length > 1
  | .ok _ => Bool.false

#guard IterationWitness.entrypoints.length == 1
