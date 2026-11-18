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
