import Noctium.Frontend

open scoped Noctium
open Noctium Noctium.Helpers

private def emptyTupleSource : Except Diagnostic Program := do
  let emptyType : Types.CompositeType := .tuple []
  let nativeType : ResultType := .scalar .native
  let base : Program := {
    ledger := [{name := "total", kind := .cell .native}]
    witnesses := [
      {name := "seed", operation := "noctium.empty-tuple-seed.v1", capability := "seed",
        result := nativeType},
      {name := "empty", operation := "noctium.empty-tuple-input.v1", capability := "empty",
        parameters := [{name := "slot", type := nativeType}], result := .composite emptyType},
      {name := "callback", operation := "noctium.empty-tuple-callback.v1", capability := "callback",
        result := nativeType}]
    declarations := [{
      id := ⟨0, 0⟩, name := "update", result := nativeType
      body := [.return (some (.native 0))]}]
    exports := [{name := "update", target := ⟨0, 0⟩}]
  }
  let empty := fun slot => Term.witnessCall s!"sequence-{slot}" "empty" [.native slot]
  let (program, mapped) ← Iteration.mapWithLimits {} base 0 [] {}
    [empty 1, empty 2]
    (.anonymous [{name := "left"}, {name := "right"}] none
      [.return (some (.witnessCall "map-callback" "callback" []))])
  let (program, folded) ← Iteration.foldWithLimits {} program 0 [] {}
    (.witnessCall "fold-initial" "seed" []) [mapped, empty 3]
    (.anonymous [{name := "acc"}, {name := "mapped"}, {name := "value"}] none
      [.return (some (.binary .add (.ref "acc") (.witnessCall "fold-callback" "callback" [])))])
  pure {program with declarations := program.declarations.map fun declaration =>
    if declaration.id == ⟨0, 0⟩ then {declaration with body := [
      .bind "sum" nativeType folded,
      .writeCell "total" .native (.disclose {} (.ref "sum")),
      .readCell "total" "after" .native,
      .return (some (.ref "after"))]}
    else declaration}

private def emptyTupleProgram : Program :=
  match emptyTupleSource with
  | .ok program => program
  | .error _ => {}

#guard emptyTupleSource.isOk

noctium_contract EmptyTupleIteration where
  cell total : Native
  entry update from emptyTupleProgram entry "update" end
end
