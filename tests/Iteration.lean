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
  Iteration.foldWithLimits {} program 0 (vectorEnv 2) {} (.uint 3 1) [mapped] typedFold

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
    (.native 1) [.ref "left"]
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

private def mixedTupleSequence : Term := .composite
  (.tuple [.scalar (.uint 7), .scalar .native]) [.uint 7 5, .native 9]

private def tupleIdentityOperator : Operator := .anonymous [
  {name := "value", type := some (.scalar .native)}]
  (some (.scalar .native)) [.return (some (.ref "value"))]

-- A heterogeneous tuple sequence joins UInt3 (max 7) and Native to Native.
#guard match Iteration.mapWithLimits {} unitMainProgram 0 [] {} [mixedTupleSequence]
    tupleIdentityOperator with
  | .ok (program, term) =>
    compilesMain program (.composite (.vector 2 (.scalar .native))) term
  | .error _ => false

private def incompatibleTupleSequence : Term := .composite
  (.tuple [.scalar .bool, .scalar .native]) [.bool true, .native 9]

#guard errorContains
  (Iteration.mapWithLimits {} unitMainProgram 0 [] {} [incompatibleTupleSequence]
    tupleIdentityOperator)
  "tuple sequence elements have no common type"

private def crossedTupleSequence : Term := .composite
  (.tuple [
    .tuple [.scalar (.uint 7), .scalar .native],
    .tuple [.scalar .native, .scalar (.uint 7)]])
  [.uint 7 1, .native 0, .native 1, .uint 7 2]

private def inferredTupleIdentity : Operator := .anonymous [{name := "pair"}] none [
  .return (some (.ref "pair"))]

private def sumTupleFold : Operator := .anonymous [
  {name := "acc", type := some (.scalar .native)}, {name := "pair"}] none [
  .return (some (.binary .add (.ref "acc")
    (.binary .add
      (.project (.ref "pair") (.tupleIndex 0))
      (.project (.ref "pair") (.tupleIndex 1)))))]

private def crossedTupleMapFold : Except Diagnostic (Program × Term) := do
  let (mappedProgram, mapped) ← Iteration.mapWithLimits {} unitMainProgram 0 [] {}
    [crossedTupleSequence] inferredTupleIdentity
  Iteration.foldWithLimits {} mappedProgram 0 [] {} (.native 0) [mapped] sumTupleFold

private def crossedTupleMapFoldRun : Except String EvalEnv := do
  let (program, term) ← crossedTupleMapFold.mapError (·.message)
  let circuit ← (Helpers.compile (installMainReturn program (.scalar .native) term) "main").mapError (·.message)
  circuit.run iterationContext []

-- The recursive join is (Native, Native) in both map inference and fold input.
#guard match crossedTupleMapFoldRun with
  | .ok values => values.lookup "result" == some (.native 4)
  | .error _ => false

private def crossedTupleBranches : Operator := .anonymous [{name := "pair"}] none [
  .branch (.eq (.project (.ref "pair") (.tupleIndex 0)) (.native 0))
    [.return (some (.composite
      (.tuple [.scalar (.uint 7), .scalar .native]) [.uint 7 1, .native 0]))]
    [.return (some (.composite
      (.tuple [.scalar .native, .scalar (.uint 7)]) [.native 1, .uint 7 2]))]]

-- Anonymous return inference joins different tuple branches before compiling the map.
#guard match Iteration.mapWithLimits {} unitMainProgram 0 [] {}
    [crossedTupleSequence] crossedTupleBranches with
  | .ok (program, term) => compilesMain program
      (.composite (.vector 2 (.tuple [.scalar .native, .scalar .native]))) term
  | .error _ => false

private def boundedNestedTupleSequence : Term := .composite
  (.tuple [
    .vector 2 (.tuple [.scalar (.uint 7), .scalar .bool]),
    .vector 2 (.tuple [.scalar (.uint 15), .scalar .bool])])
  [.uint 7 3, .bool true, .uint 7 5, .bool false,
    .uint 15 9, .bool true, .uint 15 11, .bool false]

-- Coercing a nested Vector/Tuple checks semantic source leaves, then casts
-- their Native physical representation. Bool remains a typed Bool leaf.
#guard match Iteration.mapWithLimits {} unitMainProgram 0 [] {}
    [boundedNestedTupleSequence] inferredTupleIdentity with
  | .ok (program, term) => compilesMain program
      (.composite (.vector 2 (.vector 2
        (.tuple [.scalar (.uint 15), .scalar .bool])))) term
  | .error _ => false

private def boundedTupleBranches : Operator := .anonymous [{name := "item"}] none [
  .branch (.eq (.ref "item") (.native 0))
    [.return (some (.composite
      (.tuple [.scalar (.uint 7), .scalar .bool]) [.uint 7 3, .bool true]))]
    [.return (some (.composite
      (.tuple [.scalar (.uint 15), .scalar .bool]) [.uint 15 5, .bool false]))]]

-- Anonymous return joins widen the UInt field and retain the Bool field type.
#guard match Iteration.mapWithLimits {} unitMainProgram 0 [] {}
    [.composite (.tuple [.scalar .native, .scalar .native]) [.native 0, .native 1]]
    boundedTupleBranches with
  | .ok (program, term) => compilesMain program
      (.composite (.vector 2 (.tuple [.scalar (.uint 15), .scalar .bool]))) term
  | .error _ => false

private def mismatchedShapeTupleSequence : Term := .composite
  (.tuple [
    .tuple [.scalar .native, .scalar .native],
    .tuple [.scalar .native]])
  [.native 1, .native 2, .native 3]

#guard errorContains
  (Iteration.mapWithLimits {} unitMainProgram 0 [] {} [mismatchedShapeTupleSequence]
    inferredTupleIdentity)
  "tuple sequence elements have no common type"

private def nominalJoinProgram : Program := {
  unitMainProgram with composites := {
    structures := [
      {id := "Join.Left", fields := [{name := "value", type := .scalar .native}]},
      {id := "Join.Right", fields := [{name := "value", type := .scalar .native}]}]}
}

private def nominalTupleSequence : Term := .composite
  (.tuple [.structure "Join.Left", .structure "Join.Right"]) [.native 1, .native 2]

#guard errorContains
  (Iteration.mapWithLimits {} nominalJoinProgram 0 [] {} [nominalTupleSequence]
    inferredTupleIdentity)
  "tuple sequence elements have no common type"

private def emptyTupleSequence : Term := .composite (.tuple []) []

private def emptyTupleNamedProgram : Program := {
  unitMainProgram with declarations := unitMainProgram.declarations ++ [
    {id := ⟨0, 1⟩, name := "emptyTupleIdentity", parameters := [⟨"value", .native⟩],
      result := .scalar .native, body := [.return (some (.ref "value"))]},
    {id := ⟨0, 2⟩, name := "emptyTupleFold", parameters := [⟨"acc", .native⟩, ⟨"value", .native⟩],
      result := .scalar .native, body := [.return (some (.ref "acc"))]}
  ]
}

private def emptyTupleMapOperator : Operator := .anonymous [
  {name := "value", type := some (.scalar .native)}] none [
  .return (some (.ref "value"))]

private def emptyTupleFoldOperator : Operator := .anonymous [
  {name := "acc", type := some (.scalar .native)},
  {name := "value", type := some (.scalar .native)}] none [
  .return (some (.ref "acc"))]

private def emptyTupleExplicitResultOperator : Operator := .anonymous [
  {name := "value"}] (some (.scalar .native)) [
  .return (some (.ref "value"))]

private def emptyTupleUnusedOperator : Operator := .anonymous [
  {name := "value"}] none [
  .return (some (.native 7))]

private def emptyTupleHelperArgumentOperator : Operator := .anonymous [
  {name := "value"}] none [
  .return (some (.call "emptyTupleIdentity" [.ref "value"]))]

private def emptyTupleIgnoredFoldOperator : Operator := .anonymous [
  {name := "acc"}, {name := "value"}] (some (.scalar (.uint 7))) [
  .return (some (.ref "acc"))]

-- Explicit parameter types and named signatures remain available for empty tuples.
#guard match Iteration.mapWithLimits {} unitMainProgram 0 [] {}
    [emptyTupleSequence] emptyTupleMapOperator with
  | .ok (program, term) =>
    compilesMain program (.composite (.vector 0 (.scalar .native))) term
  | .error _ => false

#guard match Iteration.mapWithLimits {} emptyTupleNamedProgram 0 [] {}
    [emptyTupleSequence] (.named "emptyTupleIdentity") with
  | .ok (program, term) =>
    compilesMain program (.composite (.vector 0 (.scalar .native))) term
  | .error _ => false

#guard match Iteration.mapWithLimits {} unitMainProgram 0 [] {}
    [emptyTupleSequence] emptyTupleExplicitResultOperator with
  | .ok (program, term) =>
    compilesMain program (.composite (.vector 0 (.scalar .native))) term
  | .error _ => false

#guard match Iteration.mapWithLimits {} unitMainProgram 0 [] {}
    [emptyTupleSequence] emptyTupleUnusedOperator with
  | .ok (program, term) =>
    compilesMain program (.composite (.vector 0 (.scalar .native))) term
  | .error _ => false

#guard match Iteration.mapWithLimits {} emptyTupleNamedProgram 0 [] {}
    [emptyTupleSequence] emptyTupleHelperArgumentOperator with
  | .ok (program, term) =>
    compilesMain program (.composite (.vector 0 (.scalar .native))) term
  | .error _ => false

#guard errorContains
  (Iteration.mapWithLimits {} unitMainProgram 0 [] {}
    [emptyTupleSequence]
    (.anonymous [{name := "value"}] none [.return (some (.ref "value"))]))
  "empty tuple callback result requires an expected type"

#guard (Iteration.mapWithLimits {} unitMainProgram 0 [] {}
    [emptyTupleSequence]
    (.anonymous [{name := "value"}] none [.return (some
      (.binary .add (.ref "value") (.native 1)))])).isOk == false

#guard (Iteration.mapWithLimits {} unitMainProgram 0 [] {}
    [emptyTupleSequence]
    (.anonymous [{name := "value"}] none [.return (some
      (.boolAnd (.ref "value") (.bool true)))])).isOk == false

#guard match Iteration.mapWithLimits {} unitMainProgram 0 [] {}
    [emptyTupleSequence]
    (.anonymous [{name := "value"}] none [.return (some (.ref "value"))])
    (expectedElement := some (.scalar .native)) with
  | .ok (program, term) =>
    compilesMain program (.composite (.vector 0 (.scalar .native))) term
  | .error _ => false

#guard match Iteration.foldWithLimits {} unitMainProgram 0 [] {}
    (.native 5) [emptyTupleSequence] emptyTupleFoldOperator with
  | .ok (program, term) => compilesMain program (.scalar .native) term
  | .error _ => false

#guard match Iteration.foldWithLimits {} emptyTupleNamedProgram 0 [] {}
    (.native 5) [emptyTupleSequence] (.named "emptyTupleFold") with
  | .ok (program, term) => compilesMain program (.scalar .native) term
  | .error _ => false

#guard match Iteration.foldWithLimits {} unitMainProgram 0 [] {}
    (.uint 3 1) [emptyTupleSequence] emptyTupleIgnoredFoldOperator with
  | .ok (program, term) => compilesMain program (.scalar (.uint 7)) term
  | .error _ => false

#guard errorContains
  (Iteration.mapWithLimits {} {emptyTupleNamedProgram with declarations :=
    emptyTupleNamedProgram.declarations ++ [{
      id := ⟨0, 3⟩, name := "emptyTupleIdentity"
      parameters := [⟨"value", .bool⟩], result := .scalar .bool
      body := [.return (some (.ref "value"))]}]} 0 [] {}
    [emptyTupleSequence] (.named "emptyTupleIdentity"))
  "ambiguous helper overload 'emptyTupleIdentity'"

private def multiSumOperator : Operator := .anonymous [
  {name := "acc", type := some (.scalar .native)},
  {name := "leftValue", type := some (.scalar .native)},
  {name := "rightValue", type := some (.scalar .native)}]
  (some (.scalar .native)) [
    .return (some (.binary .add
      (.binary .add (.ref "acc") (.ref "leftValue")) (.ref "rightValue")))]

private def multiSequenceFold : Except Diagnostic (Program × Term) :=
  Iteration.foldWithLimits {} (vectorProgram 2) 0 (vectorEnv 2) {}
    (.native 0) [.ref "left", .ref "right"] multiSumOperator

-- A fold zips two equal-length sequences, and rejects mismatched lengths.
#guard match multiSequenceFold with
  | .ok (program, term) => compilesMain program (.scalar .native) term
  | .error _ => false

#guard errorContains
  (Iteration.foldWithLimits {} (vectorProgram 3) 0 (vectorEnv 3) {}
    (.native 0) [.ref "left", .ref "right"] multiSumOperator)
  "length"

private def byteIdentityOperator : Operator := .anonymous [
  {name := "byte", type := some (.scalar .native)}]
  (some (.scalar .native)) [.return (some (.cast .native (.ref "byte")))]

private def byteSumOperator : Operator := .anonymous [
  {name := "acc", type := some (.scalar .native)},
  {name := "byte", type := some (.scalar .native)}]
  (some (.scalar .native)) [
    .return (some (.binary .add (.ref "acc") (.cast .native (.ref "byte"))))]

private def scalarBytesSequence : Term :=
  .bytes (.bytesLiteral 3 [1, 2, 3]) []

private def compositeBytesSequence : Term :=
  .composite (.bytes 3) [.native 1, .native 2, .native 3]

private def emptyScalarBytesSequence : Term :=
  .bytes (.bytesLiteral 0 []) []

private def byteMapAndFoldCompile (sequence : Term) : Bool :=
  match Iteration.mapWithLimits {} unitMainProgram 0 [] {} [sequence] byteIdentityOperator with
  | .ok (mapProgram, mapped) =>
    compilesMain mapProgram (.composite (.vector 3 (.scalar .native))) mapped &&
      match Iteration.foldWithLimits {} unitMainProgram 0 [] {} (.native 0)
        [sequence] byteSumOperator with
      | .ok (foldProgram, folded) => compilesMain foldProgram (.scalar .native) folded
      | .error _ => false
  | .error _ => false

-- Scalar Bytes and composite byte layouts each feed map and fold.
#guard byteMapAndFoldCompile scalarBytesSequence
#guard byteMapAndFoldCompile compositeBytesSequence

private def emptyBytesFoldProgram : Program := {
  unitMainProgram with declarations := unitMainProgram.declarations ++ [{
    id := ⟨0, 1⟩
    name := "failInitial"
    result := .scalar .native
    body := [.assert (.bool false), .return (some (.native 0))]
  }]
}

private def emptyBytesFoldCircuit : Except Diagnostic Circuit := do
  let (program, term) ← Iteration.foldWithLimits {} emptyBytesFoldProgram 0 [] {}
    (.call "failInitial" []) [emptyScalarBytesSequence] byteSumOperator
  Helpers.compile (installMainReturn program (.scalar .native) term) "main"

private def emptyBytesFoldRun : Except String EvalEnv :=
  match emptyBytesFoldCircuit with
  | .ok circuit => circuit.run iterationContext []
  | .error diagnostic => .error diagnostic.message

-- Empty byte folds still evaluate their initial expression.
#guard emptyBytesFoldCircuit.isOk
#guard match emptyBytesFoldRun with
  | .error "helper assertion failed" => true
  | _ => false

private def enumChoiceType : Types.CompositeType := .enumeration "Iteration.Choice"
private def enumPayloadType : Types.CompositeType := .structure "Iteration.Payload"
private def enumResultType : Types.CompositeType := .structure "Iteration.EnumResult"

private def enumMapComposites : Types.CompositeEnv := {
  structures := [
    {id := "Iteration.Payload", fields := [
      {name := "values", type := .vector 2 (.scalar .native)}]},
    {id := "Iteration.EnumResult", fields := [
      {name := "choice", type := enumChoiceType}]}]
  enumerations := [{id := "Iteration.Choice", variants := [
    {name := "Empty"},
    {name := "Filled", fields := [{name := "payload", type := enumPayloadType}]}]}]
}

private def enumMapProgram : Program :=
  {unitMainProgram with composites := enumMapComposites}

private def enumInputSequence : Term :=
  .composite (.vector 2 (.scalar .native)) [.native 0, .native 1]

private def enumResult (tag first second : Term) : Term :=
  .composite enumResultType [tag, first, second]

private def enumMapOperator : Operator := .anonymous [{name := "value"}] none [
  .return (some (.ite (.eq (.ref "value") (.native 0))
    (enumResult (.native 0) (.native 0) (.native 0))
    (enumResult (.native 1) (.ref "value") (.binary .add (.ref "value") (.native 1)))))]

private def enumMapCircuit (sequence : Term) (operator : Operator) : Except Diagnostic Circuit := do
  let (program, term) ← Iteration.mapWithLimits {} enumMapProgram 0 [] {} [sequence] operator
  Helpers.compile (installMainReturn program
    (.composite (.vector 2 enumResultType)) term) "main"

private def enumMapRun : Except String EvalEnv :=
  match enumMapCircuit enumInputSequence enumMapOperator with
  | .ok circuit => circuit.run iterationContext []
  | .error diagnostic => .error diagnostic.message

-- Map returns an empty and a filled nested enum. The empty variant's padded
-- payload stays canonical, while the filled variant preserves its nested vector.
#guard (enumMapCircuit enumInputSequence enumMapOperator).isOk
#guard match enumMapRun with
  | .ok values =>
    values.lookup "result.0.choice.$tag" == some (.native 0) &&
    values.lookup "result.0.choice.$payload0" == some (.native 0) &&
    values.lookup "result.0.choice.$payload1" == some (.native 0) &&
    values.lookup "result.1.choice.$tag" == some (.native 1) &&
    values.lookup "result.1.choice.$payload0" == some (.native 1) &&
    values.lookup "result.1.choice.$payload1" == some (.native 2)
  | .error _ => false

#guard errorContains
  (Iteration.mapWithLimits {maxSourceNodes := 100} enumMapProgram 0 [] {}
    [enumInputSequence] enumMapOperator)
  "source nodes"

private def enumInactivePayloadOperator : Operator := .anonymous [{name := "value"}] none [
  .return (some (.ite (.eq (.ref "value") (.native 0))
    (enumResult (.native 0) (.native 0) (.native 0))
    (enumResult (.native 1) (.cast (.uint 7) (.native 8)) (.native 0))))]

private def enumInactivePayloadCircuit : Except Diagnostic Circuit :=
  enumMapCircuit (.composite (.vector 2 (.scalar .native)) [.native 0, .native 0])
    enumInactivePayloadOperator

-- An inactive filled-variant payload does not evaluate its failing cast.
#guard (enumInactivePayloadCircuit).isOk
#guard match (enumInactivePayloadCircuit.mapError (·.message)).bind
    (fun circuit => circuit.run iterationContext []) with
  | .ok values =>
    values.lookup "result.0.choice.$tag" == some (.native 0) &&
    values.lookup "result.0.choice.$payload0" == some (.native 0) &&
    values.lookup "result.0.choice.$payload1" == some (.native 0)
  | .error _ => false
