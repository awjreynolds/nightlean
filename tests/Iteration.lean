import Noctium.Helpers.Iteration

open Noctium
open Noctium.Helpers
open Noctium.Helpers.Iteration

private def errorContains (value : Except Diagnostic α) (text : String) : Bool :=
  match value with
  | .error diagnostic => (diagnostic.message.splitOn text).length > 1
  | .ok _ => false

private def installMainReturn (program : Program) (type : ResultType) (value : Term) : Program :=
  {program with declarations := program.declarations.map fun declaration =>
    if declaration.id == ⟨0, 0⟩ then
      {declaration with result := type, body := [.return (some value)]}
    else declaration}

private def compilesMain (program : Program) (type : ResultType) (value : Term) : Bool :=
  (Helpers.compile (installMainReturn program type value) "main").isOk

private def scalarProgram : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "main", parameters := [⟨"x", .native⟩, ⟨"offset", .native⟩],
      result := .scalar .native, body := [.return (some (.ref "x"))]},
    {id := ⟨0, 1⟩, name := "f", parameters := [⟨"value", .native⟩],
      result := .scalar .native, body := [.return (some (.ref "value"))]}
  ]
  exports := [{name := "main", target := ⟨0, 0⟩, inputs := [
    {name := "x", ty := .native, visibility := .public},
    {name := "offset", ty := .native, visibility := .public}]}]
}

private def scalarEnv : Environment := [
  ("x", .scalar .native), ("offset", .scalar .native)]

private def inferredAddOffset : Operator := .anonymous [{name := "value"}] none [
  .return (some (.binary .add (.ref "value") (.ref "offset")))]

-- Anonymous signatures infer from the argument and return body. Free values become captures.
#guard match Iteration.applyWithLimits {} scalarProgram 0 scalarEnv {} inferredAddOffset [.ref "x"] with
  | .ok (program, term) =>
    program.declarations.any (fun declaration => declaration.name != "main" && declaration.name != "f" &&
      declaration.parameters.map (·.name) == ["offset", "value"] &&
      declaration.parameters.all (fun parameter => declaration.parameterType parameter == .scalar .native) &&
      declaration.result == .scalar .native) &&
      compilesMain program (.scalar .native) term
  | .error _ => false

-- Named operators lower to ordinary checked helper calls.
#guard match Iteration.applyWithLimits {} scalarProgram 0 scalarEnv {} (.named "f") [.ref "x"] with
  | .ok (program, .call "f" [.ref "x"]) => compilesMain program (.scalar .native) (.call "f" [.ref "x"])
  | _ => false

#guard errorContains
  (Iteration.applyWithLimits {} scalarProgram 0 scalarEnv {} (.anonymous [{name := "value"}] none
    [.return (some (.ref "missing"))]) [.ref "x"])
  "unknown helper value 'missing'"

private def shadowEnv : Environment := [
  ("f", .scalar .native), ("x", .scalar .native), ("offset", .scalar .native)]

#guard errorContains
  (Iteration.applyWithLimits {} scalarProgram 0 shadowEnv {} (.named "f") [.ref "x"])
  "hidden by a value binding"

-- A global call stays hidden by caller value `f`, even without a reference to that value.
#guard errorContains
  (Iteration.applyWithLimits {} scalarProgram 0 shadowEnv {}
    (.anonymous [{name := "value"}] none
      [.return (some (.call "f" [.ref "value"]))]) [.ref "x"])
  "hidden by a value binding"

private def nativeVector (length : Nat) : Types.CompositeType :=
  .vector length (.scalar .native)

private def vectorProgram (rightLength : Nat) : Program := Id.run do
  let leftType := nativeVector 2
  let rightType := nativeVector rightLength
  return {
    declarations := [{
      id := ⟨0, 0⟩, name := "main",
      parameters := [⟨"left", .native⟩, ⟨"right", .native⟩],
      compositeParameters := [("left", leftType), ("right", rightType)],
      result := .scalar (.uint 7), body := [.return (some (.uint 7 0))]}]
    exports := [{name := "main", target := ⟨0, 0⟩, compositeInputs := [
      {name := "left", type := leftType, visibility := .public},
      {name := "right", type := rightType, visibility := .public}]}]
  }

private def vectorEnv (rightLength : Nat) : Environment := [
  ("left", .composite (nativeVector 2)), ("right", .composite (nativeVector rightLength))]

private def pairSum : Operator := .anonymous [{name := "leftValue"}, {name := "rightValue"}] none [
  .return (some (.binary .add (.ref "leftValue") (.ref "rightValue")))]

private def typedFold : Operator := .anonymous [
  {name := "acc", type := some (.scalar (.uint 7))},
  {name := "value", type := some (.scalar .native)}]
  (some (.scalar (.uint 7))) [
    .return (some (.cast (.uint 7)
      (.binary .add (.ref "acc") (.cast (.uint 7) (.ref "value")))))]

private def mapThenFold : Except Diagnostic (Program × Term) := do
  let (program, mapped) ← Iteration.mapWithLimits {} (vectorProgram 2) 0 (vectorEnv 2) {}
    [.ref "left", .ref "right"] pairSum
  Iteration.foldWithLimits {} program 0 (vectorEnv 2) {} (.uint 3 1) mapped typedFold

-- Equal-length vector map and a narrower initial value compile through Helpers.
#guard match mapThenFold with
  | .ok (program, term) =>
    program.declarations.any (fun declaration =>
      declaration.result == .scalar (.uint 7) && match declaration.parameters with
      | first :: _ => declaration.parameterType first == .scalar (.uint 7)
      | [] => false) && compilesMain program (.scalar (.uint 7)) term
  | .error _ => false

#guard errorContains
  (Iteration.mapWithLimits {} (vectorProgram 3) 0 (vectorEnv 3) {}
    [.ref "left", .ref "right"] pairSum)
  "length"

-- Empty vectors retain their element type while the map makes no iterations.
private def emptyVectorType : Types.CompositeType := nativeVector 0
private def emptyVectorProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "main"
    parameters := [⟨"values", .native⟩]
    compositeParameters := [("values", emptyVectorType)]
    result := .composite emptyVectorType
    body := [.return (some (.ref "values"))]
  }]
  exports := [{
    name := "main"
    target := ⟨0, 0⟩
    compositeInputs := [{name := "values", type := emptyVectorType, visibility := .public}]
  }]
}

#guard match Iteration.mapWithLimits {} emptyVectorProgram 0
    [("values", .composite emptyVectorType)] {} [.ref "values"]
    (.anonymous [{name := "value"}] none [.return (some (.ref "value"))]) with
  | .ok (program, term) => compilesMain program (.composite emptyVectorType) term
  | .error _ => false

#guard errorContains
  (Iteration.foldWithLimits {} (vectorProgram 2) 0 (vectorEnv 2) {}
    (.native 1) (.ref "left")
    (.anonymous [{name := "acc"}, {name := "value"}] none [.return (some (.bool true))]))
  "accumulator"

private def mapResultType : Types.CompositeType := .structure "Iteration.Item"

private def mapResultComposites : Types.CompositeEnv := {
  structures := [{id := "Iteration.Item", fields := [
    {name := "amount", type := .scalar .native},
    {name := "metadata", type := .vector 2 (.scalar .native)}]}]
}

private def mapResultProgram : Program :=
  {vectorProgram 2 with composites := mapResultComposites}

private def recordMap : Operator := .anonymous [{name := "value"}] none [
  .return (some (.composite mapResultType [.ref "value", .ref "value", .ref "value"]))]

-- Map preserves nested record layout through the real Helpers compiler.
#guard match Iteration.mapWithLimits {} mapResultProgram 0 (vectorEnv 2) {}
    [.ref "left"] recordMap with
  | .ok (program, term) =>
    compilesMain program (.composite (.vector 2 mapResultType)) term
  | .error _ => false

private def booleanMap : Operator := .anonymous [{name := "value"}] none [
  .return (some (.eq (.ref "value") (.native 0)))]

-- Scalar Bool results map through the checked composite layout.
#guard match Iteration.mapWithLimits {} (vectorProgram 2) 0 (vectorEnv 2) {}
    [.ref "left"] booleanMap with
  | .ok (program, term) =>
    compilesMain program (.composite (.vector 2 (.scalar .bool))) term
  | .error _ => false

private def iterationContext : EvalContext := {
  modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "hash unavailable"}

private def unitMapProgram : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "main", result := .unit, body := [.return none]},
    {id := ⟨0, 1⟩, name := "failUnit", result := .unit,
      body := [.assert (.bool false), .return none]}]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}

private def failingUnitMap (length : Nat) : Except String EvalEnv := do
  let sequenceType := nativeVector length
  let sequence := .composite sequenceType (List.replicate length (.native 1))
  let operator := .anonymous [{name := "value"}] none [
    .evaluate (.call "failUnit" []), .return none]
  let (program, term) ← (Iteration.mapWithLimits {} unitMapProgram 0 [] {}
    [sequence] operator).mapError (·.message)
  let circuit ← (Helpers.compile
    (installMainReturn program (.composite (.vector length .unit)) term) "main").mapError (·.message)
  circuit.run iterationContext []

-- A Unit result keeps the callback's assertion. Empty maps still typecheck the
-- callback without running it.
#guard match failingUnitMap 1 with | .error _ => true | _ => false
#guard match failingUnitMap 0 with | .ok _ => true | _ => false

private def failEmptyProgram : Program := {
  declarations := [
    {id := ⟨0, 0⟩, name := "main", result := .unit, body := [.return none]},
    {id := ⟨0, 1⟩, name := "failEmpty", result := .composite (nativeVector 0),
      body := [.evaluate (.cast (.uint 7) (.native 8)),
        .return (some (.composite (nativeVector 0) []))]}]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}

private def emptyMapSequenceCircuit : Except Diagnostic Circuit := do
  let (program, term) ← Iteration.mapWithLimits {} failEmptyProgram 0 [] {}
    [.call "failEmpty" []]
    (.anonymous [{name := "value"}] none [.return (some (.ref "value"))])
  Helpers.compile (installMainReturn program (.composite (nativeVector 0)) term) "main"

private def emptyMapEvaluatesSequence : Except String EvalEnv :=
  match emptyMapSequenceCircuit with
  | .ok circuit => circuit.run iterationContext []
  | .error diagnostic => .error diagnostic.message

-- The sequence expression runs once even when the resulting vector is empty.
#guard emptyMapSequenceCircuit.isOk
#guard match emptyMapEvaluatesSequence with
  | .error "scalar conversion exceeds unsigned bound" => true
  | _ => false

private def unusedNarrowingGuardProgram : Program := {
  ledger := [{name := "total", kind := .cell .native}]
  declarations := [{
    id := ⟨0, 0⟩
    name := "update"
    parameters := [⟨"enabled", .bool⟩, ⟨"amount", .native⟩]
    result := .unit
    body := [
      .branch (.ref "enabled") [
        .bind "unused" (.scalar (.uint 7)) (.cast (.uint 7) (.ref "amount")),
        .writeCell "total" .native (.native 1)] [],
      .return none]
  }]
  exports := [{name := "update", target := ⟨0, 0⟩, inputs := [
    {name := "enabled", ty := .bool, visibility := .public},
    {name := "amount", ty := .native, visibility := .public}]}]
}

private def unusedNarrowingGuard (enabled : Bool) : Except String Bool := do
  let entry ← (Helpers.compileEntrypointFor unusedNarrowingGuardProgram "update"
    unusedNarrowingGuardProgram.ledger).mapError (·.message)
  let some index := entry.effects.findIdx? (fun effect =>
    match effect with
    | .writeCell .. => true
    | _ => false)
    | throw "missing public write effect"
  let some (some guard) := entry.effectGuards[index]?
    | throw "missing ledger effect guard"
  guard.eval iterationContext [
    ("enabled", .bool enabled), ("amount", .native 8)]

-- A discarded narrowing cast stays in the active public-write guard. Its
-- totalized form skips the cast when the branch is inactive.
#guard (Helpers.compileEntrypointFor unusedNarrowingGuardProgram "update"
  unusedNarrowingGuardProgram.ledger).isOk
#guard match unusedNarrowingGuard true with
  | .error "scalar conversion exceeds unsigned bound" => true
  | _ => false
#guard match unusedNarrowingGuard false with
  | .ok Bool.false => true
  | _ => false

private def unitMainProgram : Program := {
  declarations := [{id := ⟨0, 0⟩, name := "main", result := .unit, body := [.return none]}]
  exports := [{name := "main", target := ⟨0, 0⟩}]
}

private def unitResultOperator : Operator := .anonymous [
  {name := "unitValue", type := some .unit}]
  (some (.scalar .native)) [.return (some (.native 7))]

-- An anonymous operator accepts a typed Unit argument and returns Native.
#guard match Iteration.applyWithLimits {} unitMainProgram 0 [] {} unitResultOperator [.unit] with
  | .ok (program, term) => compilesMain program (.scalar .native) term
  | .error _ => false

private def unitRootProgram : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "main"
    parameters := [⟨"marker", .native⟩]
    compositeParameters := [("marker", .unit)]
    result := .unit
    body := [.return none]
  }]
  exports := [{
    name := "main"
    target := ⟨0, 0⟩
    compositeInputs := [{name := "marker", type := .unit, visibility := .public}]
  }]
}

-- A Unit root input has a declared aggregate parameter but no Native fields.
#guard match Helpers.compile unitRootProgram "main" with
  | .ok circuit => circuit.inputs.isEmpty
  | .error _ => false

private def unitRootWithoutParameter : Program := {
  unitRootProgram with declarations := unitRootProgram.declarations.map fun declaration =>
    {declaration with parameters := [], compositeParameters := []}
}

#guard !(Helpers.compile unitRootWithoutParameter "main").isOk

private def capturedUnitApply : Except Diagnostic (Program × Term) :=
  Iteration.applyWithLimits {} unitRootProgram 0 [("marker", .unit)] {}
    (.anonymous [{name := "argument", type := some .unit}]
      (some (.scalar .native)) [
        .evaluate (.ref "marker"), .return (some (.native 3))]) [.unit]

-- A closure captures the bound Unit root value and compiles with zero input fields.
#guard match capturedUnitApply with
  | .ok (program, term) => compilesMain program (.scalar .native) term
  | .error _ => false

private def unitVectorType : Types.CompositeType := .vector 2 .unit
private def unitVector : Term := .composite unitVectorType []

private def unitMapOperator : Operator := .anonymous [
  {name := "item", type := some .unit}]
  (some (.scalar .native)) [.return (some (.native 11))]

-- Mapping Unit elements passes the typed Unit argument and builds Native results.
#guard match Iteration.mapWithLimits {} unitMainProgram 0 [] {} [unitVector] unitMapOperator with
  | .ok (program, term) =>
    compilesMain program (.composite (.vector 2 (.scalar .native))) term
  | .error _ => false

private def strictUnitArgumentProgram : Program := {
  declarations := unitMainProgram.declarations ++ [{
    id := ⟨0, 1⟩
    name := "failUnit"
    result := .unit
    body := [.assert (.bool false), .return none]
  }]
  exports := unitMainProgram.exports
}

private def strictUnitArgumentCircuit : Except Diagnostic Circuit := do
  let (program, term) ← Iteration.applyWithLimits {} strictUnitArgumentProgram 0 [] {}
    unitResultOperator [.call "failUnit" []]
  Helpers.compile (installMainReturn program (.scalar .native) term) "main"

private def strictUnitArgumentRun : Except String EvalEnv :=
  match strictUnitArgumentCircuit with
  | .ok circuit => circuit.run iterationContext []
  | .error diagnostic => .error diagnostic.message

-- Compilation succeeds, then strict evaluation of a computed Unit argument fails.
#guard strictUnitArgumentCircuit.isOk
#guard match strictUnitArgumentRun with
  | .error "helper assertion failed" => true
  | _ => false
