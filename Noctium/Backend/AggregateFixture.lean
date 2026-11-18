import Noctium.Types.ValueExpressions
import Noctium.Backend.Zkir
import Noctium.Types.ValueSchema

/-! Typed-backend qualification only. Source aggregate effects remain gated by DF-01. -/
namespace Noctium.Backend.AggregateFixture
open Lean Types

def environment : CompositeEnv := {
  structures := [{id := "Demo.Note", fields := [
    ⟨"amount", .scalar (.uint 255), {}⟩, ⟨"flag", .scalar .bool, {}⟩]}]
  enumerations := [{id := "Demo.Choice", variants := [
    {name := "Full", fields := [⟨"flag", .scalar .bool, {}⟩, ⟨"amount", .scalar (.uint 15), {}⟩]},
    {name := "Native", fields := [⟨"value", .scalar .native, {}⟩]}, {name := "Empty"}]}]
}

def type : CompositeType := .tuple [
  .structure "Demo.Note", .vector 2 (.scalar (.uint 255)), .enumeration "Demo.Choice",
  .bytes 2, .unit, .vector 0 (.scalar .bool)]

private def compile (type : CompositeType) : Except String CompiledType :=
  (compileType environment type).mapError (·.message)

private def input (name : String) (visibility : Visibility) : Input :=
  {name, ty := .native, visibility}

/-- Expected leaves are public parameters and equal the disclosed computed
leaves. Both sequences are bound by the existing producer's Impact schedule. -/
def circuit : Except String Circuit := do
  let compiled ← compile type
  let privateInputs := (List.range compiled.checked.expandedLeaves).map fun i => input s!"leaf{i}" .«private»
  let expectedInputs := (List.range (compiled.checked.expandedLeaves + 1)).map fun i => input s!"expected{i}" .«public»
  let inputs := privateInputs ++ [input "index" .«private»] ++ expectedInputs
  let types := inputs.map fun i => (i.name, i.ty)
  let leaves := (List.range compiled.checked.expandedLeaves).map fun i => Expr.ref s!"leaf{i}"
  let value ← checkNativeExpression compiled types leaves
  let vector ← compile (.vector 2 (.scalar (.uint 255)))
  let pair ← checkNativeExpression vector types [.ref "leaf2", .ref "leaf3"]
  let selected ← indexNativeVector vector pair types (.ref "index") [[], []] []
  let results := leaves ++ selected.value.leaves
  let constraints := value.constraints ++ selected.value.constraints ++
    (results.zipIdx.map fun (leaf, i) => Expr.eq leaf (.ref s!"expected{i}"))
  let outputs := results.zipIdx.map fun (leaf, i) =>
    {name := s!"result{i}", ty := Ty.native, value := Expr.disclose {} leaf : Output}
  pure {name := "aggregate", inputs, constraints, outputs}

private def witness (id : String) (privateLeaves expected : List Nat) (index : Nat) (accepted : Bool) : Json :=
  let publicLeaves := expected.map toString
  Json.mkObj [("id", toJson id), ("circuit", toJson ("aggregate" : String)),
    ("private", toJson ((privateLeaves ++ [index]).map toString)),
    ("publicInputs", toJson (publicLeaves ++ publicLeaves)), ("publicReads", toJson publicLeaves),
    ("activityGroups", toJson (expected.length + 1)), ("accepted", toJson accepted)]

def cases : List Json := Id.run do
  let full := [200, 1, 3, 4, 0, 1, 7, 255, 0]
  let native := [200, 1, 3, 4, 1, Field.modulus - 1, 0, 255, 0]
  let empty := [200, 1, 3, 4, 2, 0, 0, 255, 0]
  return [
    witness "TYV-NESTED" full (full ++ [4]) 1 true,
    witness "TYV-NATIVE-MIXED-ENUM" native (native ++ [3]) 0 true,
    witness "TYV-EMPTY-ENUM" empty (empty ++ [4]) 1 true,
    witness "TYV-CHANGED-PUBLIC-LEAF" full (full.set 0 201 ++ [4]) 1 false,
    witness "TYV-INVALID-TAG" (full.set 4 3) (full.set 4 3 ++ [4]) 1 false,
    witness "TYV-ACTIVE-BOOL" (full.set 5 2) (full.set 5 2 ++ [4]) 1 false,
    witness "TYV-ACTIVE-UINT" (full.set 6 16) (full.set 6 16 ++ [4]) 1 false,
    witness "TYV-INACTIVE-PADDING" (native.set 6 1) (native.set 6 1 ++ [3]) 0 false,
    witness "TYV-EMPTY-PADDING" (empty.set 5 1) (empty.set 5 1 ++ [4]) 1 false,
    witness "TYV-INDEX-BOUNDS" full (full ++ [0]) 2 false,
    witness "TYV-SELECTED-LEAF" full (full ++ [3]) 1 false,
    witness "TYV-SCALAR-BOUND" (full.set 0 256) (full.set 0 256 ++ [4]) 1 false,
    witness "TYV-BYTE-BOUND" (full.set 7 256) (full.set 7 256 ++ [4]) 1 false]

end Noctium.Backend.AggregateFixture

open Noctium.Backend.AggregateFixture in
def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "Usage: lean --run Noctium/Backend/AggregateFixture.lean DIRECTORY")
  let circuit ← IO.ofExcept circuit
  let relation ← IO.ofExcept ((Noctium.Backend.Zkir.lowerCircuit circuit).mapError (·.message))
  let compiled ← IO.ofExcept ((Noctium.Types.compileType environment type).mapError (·.message))
  let schema ← IO.ofExcept (Noctium.Types.schemaJson compiled)
  IO.FS.createDirAll directory
  let directory := System.FilePath.mk directory
  IO.FS.writeFile (directory / "aggregate.zkir") (relation.pretty ++ "\n")
  IO.FS.writeFile (directory / "cases.json") ((Lean.toJson cases).pretty ++ "\n")
  IO.FS.writeFile (directory / "native-schema.json") (schema.pretty ++ "\n")
  IO.println s!"aggregate native fixture: {compiled.checked.expandedLeaves} checked leaves, {cases.length} raw witness cases"
