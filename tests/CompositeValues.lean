import Noctium.Types.ValueSchema
import Noctium.Types.ValueViews
import Noctium.Types.ValueExpressions

open Noctium Noctium.Types

def aggregateEnvironment : CompositeEnv := {
  structures := [
    {id := "Demo.Note", fields := [⟨"amount", .scalar (.uint 255), {}⟩, ⟨"flag", .scalar .bool, {}⟩]},
    {id := "Other.Note", fields := [⟨"amount", .scalar (.uint 255), {}⟩, ⟨"flag", .scalar .bool, {}⟩]}]
  enumerations := [{id := "Demo.Choice", variants := [
    {name := "Full", fields := [⟨"flag", .scalar .bool, {}⟩, ⟨"amount", .scalar (.uint 15), {}⟩]},
    {name := "Native", fields := [⟨"value", .scalar .native, {}⟩]},
    {name := "Empty"}]}]
}

def aggregateType : CompositeType := .tuple [
  .structure "Demo.Note", .vector 2 (.scalar (.uint 255)), .enumeration "Demo.Choice",
  .bytes 2, .unit, .vector 0 (.scalar .bool)]

def aggregateValue : AggregateValue := .tuple [
  .structure "Demo.Note" [("amount", .scalar (.uint 255) 200), ("flag", .scalar .bool 1)],
  .vector [.scalar (.uint 255) 3, .scalar (.uint 255) 4],
  .enumeration "Demo.Choice" "Full" [("flag", .scalar .bool 1), ("amount", .scalar (.uint 15) 7)],
  .bytes [255, 0], .unit, .vector []]

private def roundtrip (type : CompositeType) (value : AggregateValue) : Except String Bool := do
  let compiled ← (compileType aggregateEnvironment type).mapError (·.message)
  let bytes ← encode compiled value
  pure ((← decode compiled bytes) == value)

private def accepted (value : Except String α) : Bool := match value with | .ok _ => true | _ => false
private def rejected (value : Except String α) : Bool := !accepted value

-- TYV-ROUNDTRIP, TYV-NESTED and TYV-EMPTY.
#guard match roundtrip aggregateType aggregateValue with | .ok true => true | _ => false
#guard match roundtrip .unit .unit with | .ok true => true | _ => false
#guard match roundtrip (.tuple []) (.tuple []) with | .ok true => true | _ => false
#guard match roundtrip (.vector 0 (.scalar .bool)) (.vector []) with | .ok true => true | _ => false
#guard match roundtrip (.bytes 0) (.bytes []) with | .ok true => true | _ => false
#guard match roundtrip (.enumeration "Demo.Choice") (.enumeration "Demo.Choice" "Empty" []) with
  | .ok true => true | _ => false
#guard match roundtrip (.enumeration "Demo.Choice")
    (.enumeration "Demo.Choice" "Native" [("value", .scalar .native (Field.modulus - 1))]) with
  | .ok true => true | _ => false

private def compiledRoot : Except String CompiledType :=
  (compileType aggregateEnvironment aggregateType).mapError (·.message)
private def compiledEnum : Except String CompiledType :=
  (compileType aggregateEnvironment (.enumeration "Demo.Choice")).mapError (·.message)

#guard match compiledRoot with | .ok type => type.checked.expandedLeaves == 9 | _ => false
#guard accepted (do let type ← compiledRoot; discard (schemaJson type))
#guard rejected (do let type ← compiledEnum; discard (unflatten type [3, 0, 0]))
#guard rejected (do let type ← compiledEnum; discard (unflatten type [0, 2, 0]))
#guard rejected (do let type ← compiledEnum; discard (unflatten type [0, 1, 16]))
#guard rejected (do let type ← compiledEnum; discard (unflatten type [1, 7, 1]))
#guard rejected (do let type ← compiledEnum; discard (unflatten type [2, 1, 0]))
#guard rejected (do let type ← compiledEnum; discard (unflatten type [2, 0]))
#guard rejected (do let type ← compiledEnum; discard (unflatten type [2, 0, 0, 0]))
#guard rejected (do let type ← compiledEnum; discard (flatten type (.enumeration "Wrong.Choice" "Empty" [])))
#guard rejected (do let type ← compiledEnum; discard (flatten type (.enumeration "Demo.Choice" "Missing" [])))
#guard rejected (do
  let type ← (compileType aggregateEnvironment (.structure "Demo.Note")).mapError (·.message)
  discard (flatten type (.structure "Other.Note" [("amount", .scalar (.uint 255) 1), ("flag", .scalar .bool 0)])))
#guard rejected (do
  let type ← (compileType aggregateEnvironment (.scalar (.uint 255))).mapError (·.message)
  discard (flatten type (.scalar (.uint 255) 256)))
#guard rejected (do
  let type ← (compileType aggregateEnvironment (.bytes 1)).mapError (·.message)
  discard (flatten type (.bytes [256])))

-- Checked projections and pattern decomposition retain their logical types.
#guard accepted (do
  let type ← compiledRoot
  let value ← checkValue type aggregateValue
  let selected ← project type value (.tupleIndex 0)
  unless selected.1.type == .structure "Demo.Note" do throw "lost nominal identity"
  let fields ← decompose selected.1 selected.2
  unless fields.map Prod.fst == ["amount", "flag"] do throw "lost field order")
#guard rejected (do
  let type ← compiledRoot
  let value ← checkValue type aggregateValue
  discard (project type value (.tupleIndex 6)))
#guard rejected (do
  let type ← (compileType aggregateEnvironment (.vector 0 (.scalar .bool))).mapError (·.message)
  let value ← checkValue type (.vector [])
  discard (project type value (.vectorIndex 0)))
#guard rejected (do
  let type ← compiledEnum
  let value ← checkValue type (.enumeration "Demo.Choice" "Empty" [])
  discard (project type value (.enumField "Full" "flag")))

private def indexOrigin : Disclosure.Origin := {name := "index", kind := .parameter, span := {file := "index.lean"}}
#guard accepted (do
  let type ← (compileType aggregateEnvironment (.vector 2 (.scalar .bool))).mapError (·.message)
  let value ← checkValue type (.vector [.scalar .bool 0, .scalar .bool 1])
  let tracked ← trackValue type value [[], []]
  let selected ← projectTracked type tracked (.vectorIndex 1) [indexOrigin]
  unless selected.indexOrigins == [indexOrigin] && selected.conservativeOrigins == [[indexOrigin]] do throw "index origin lost")
#guard accepted (do
  let type ← (compileType aggregateEnvironment (.vector 1 .unit)).mapError (·.message)
  let value ← checkValue type (.vector [.unit])
  let tracked ← trackValue type value []
  let selected ← projectTracked type tracked (.vectorIndex 0) [indexOrigin]
  unless selected.indexOrigins == [indexOrigin] do throw "empty value erased index origin")

-- Reconstruction exposes the exact canonical flattening result.
#guard accepted (do
  let type ← compiledRoot
  let value ← unflattenChecked type [200, 1, 3, 4, 0, 1, 7, 255, 0]
  unless value.value == aggregateValue do throw "reconstruction changed value")

private def evaluationContext : EvalContext := {
  modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused hash oracle"}

private def validateNativeEnum (leaves : List Nat) : Except String Unit := do
  let type ← compiledEnum
  let expression ← checkNativeExpression type [] (leaves.map Expr.native)
  runConstraints evaluationContext [] expression.constraints

#guard accepted (validateNativeEnum [0, 1, 15])
#guard accepted (validateNativeEnum [1, Field.modulus - 1, 0])
#guard accepted (validateNativeEnum [2, 0, 0])
#guard rejected (validateNativeEnum [0, 2, 0])
#guard rejected (validateNativeEnum [0, 1, 16])
#guard rejected (validateNativeEnum [1, 7, 1])
#guard rejected (validateNativeEnum [2, 1, 0])
#guard rejected (validateNativeEnum [3, 0, 0])

private def indexedUnit (index : Nat) : Except String NativeSelection := do
  let type ← (compileType aggregateEnvironment (.vector 2 .unit)).mapError (·.message)
  let expression ← checkNativeExpression type [] []
  indexNativeVector type expression [] (.native index) [] [indexOrigin] [indexOrigin]

#guard accepted (do
  let selected ← indexedUnit 1
  runConstraints evaluationContext [] selected.value.constraints
  unless selected.indexOrigins == [indexOrigin] && selected.controlOrigins == [indexOrigin] do
    throw "zero-leaf selection erased index/control origins")
#guard rejected (do
  let selected ← indexedUnit 2
  runConstraints evaluationContext [] selected.value.constraints)
#guard rejected (do
  let type ← (compileType aggregateEnvironment (.vector 0 .unit)).mapError (·.message)
  let expression ← checkNativeExpression type [] []
  discard (indexNativeVector type expression [] (.native 0) [] []))
#guard accepted (do
  let type ← compiledRoot
  let value ← checkValue type aggregateValue
  let expression ← literal type value
  let checked ← checkExpression type [] expression
  let evaluated ← evaluateExpression type [] checked evaluationContext []
  unless evaluated.value == value.value && evaluated.leaves == value.leaves do
    throw "expression evaluation disagrees with canonical flattening")

-- A raw backend carrier's caller-supplied constraint list is never trusted.
#guard rejected (do
  let type ← (compileType aggregateEnvironment (.vector 2 (.scalar (.uint 255)))).mapError (·.message)
  let raw ← checkNativeExpression type [] [.native 256, .native 0]
  let forged := {raw with constraints := []}
  let selected ← indexNativeVector type forged [] (.native 1) [[], []] []
  runConstraints evaluationContext [] selected.value.constraints)

private def chainedIndex (element : CompositeType) (leaves : List Nat) (first second : Nat) :
    Except String Unit := do
  let type ← (compileType aggregateEnvironment (.vector 2 (.vector 2 element))).mapError (·.message)
  let raw ← checkNativeExpression type [] (leaves.map Expr.native)
  let selected ← indexNativeVector type raw [] (.native first)
    (List.replicate leaves.length []) []
  let nested ← indexNativeVector selected.type selected.value [] (.native second)
    selected.componentOrigins []
  runConstraints evaluationContext [] nested.value.constraints

-- An earlier failed index remains an obligation through a later selection.
#guard accepted (chainedIndex .unit [] 1 0)
#guard rejected (chainedIndex .unit [] 2 0)
#guard accepted (chainedIndex (.scalar (.uint 255)) [1, 2, 3, 4] 1 0)
#guard rejected (chainedIndex (.scalar (.uint 255)) [1, 2, 3, 4] 2 0)

private def hex (bytes : ByteArray) : String :=
  String.join (bytes.data.toList.map fun byte =>
    let digits := "0123456789abcdef".toList.toArray
    String.singleton digits[byte.toNat / 16]! ++ String.singleton digits[byte.toNat % 16]!)

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "Usage: lean --run tests/CompositeValues.lean FIXTURE_DIRECTORY")
  let type ← IO.ofExcept compiledRoot
  let value ← IO.ofExcept (checkValue type aggregateValue)
  let schema ← IO.ofExcept (schemaJson type)
  let json ← IO.ofExcept (valueJson type value)
  let wire ← IO.ofExcept (encode type aggregateValue)
  IO.FS.createDirAll directory
  IO.FS.writeFile (System.FilePath.mk directory / "schema.json") (schema.pretty ++ "\n")
  IO.FS.writeFile (System.FilePath.mk directory / "value.json") (json.pretty ++ "\n")
  IO.FS.writeFile (System.FilePath.mk directory / "wire.hex") (hex wire ++ "\n")
  IO.FS.writeFile (System.FilePath.mk directory / "leaves.json") ((Lean.toJson (value.leaves.map toString)).pretty ++ "\n")
  IO.println s!"aggregate fixture: {value.leaves.length} checked leaves, {wire.size} wire bytes"
