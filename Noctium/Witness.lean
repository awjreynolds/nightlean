import Noctium.Control
import Noctium.Backend.Zkir

namespace Noctium.Witness
open Lean Helpers

private def fail (span : SourceSpan) (message : String) : Except Diagnostic α :=
  .error {span, message}

/-- Private stages remain in the host plan. Their computations remain in the
constraint program, without claiming the private write is circuit-proved. -/
def eraseStages : List Statement → List Statement
  | [] => []
  | .stage _ _ _ value :: rest => .evaluate value :: eraseStages rest
  | .branch condition yes no :: rest =>
    .branch condition (eraseStages yes) (eraseStages no) :: eraseStages rest
  | statement :: rest => statement :: eraseStages rest
termination_by body => sizeOf body

def eraseProgram (program : Program) : Program :=
  Helpers.mapDeclarationBodies eraseStages program

private def scalarName : Ty → String
  | .native => "Native"
  | .bool => "Bool"
  | .uint maximum => s!"UIntRange<{maximum + 1}>"
  | .bytes 32 => "Bytes<32>"
  | .bytes length => s!"Bytes<{length}>"
  | .jubjubScalar => "JubjubScalar"
  | .jubjubPoint => "JubjubPoint"

private def idName (id : DeclarationId) : String := s!"s{id.scope}d{id.ordinal}"

private def setField (json : Json) (name : String) (value : Json) : Except Diagnostic Json := do
  let object ← (json.getObj?).mapError fun _ => {span := {}, message := "invalid witness artifact object"}
  pure (Json.mkObj ((object.toList.filter (·.1 != name)) ++ [(name, value)]))

private def arrayField (json : Json) (name : String) : Except Diagnostic (Array Json) :=
  ((json.getObjVal? name).bind Json.getArr?).mapError fun _ =>
    {span := {}, message := "missing typed control metadata"}

private def resultToken (program : Program) (plan : Json) (span : SourceSpan)
    (type : ResultType) : Except Diagnostic String := do
  match type with
  | .unit => pure "Unit"
  | .scalar type => pure (scalarName type)
  | .composite type =>
    let compiled ← (Types.compileType program.composites type).mapError fun diagnostic =>
      {span, message := diagnostic.message}
    for entry in (← arrayField plan "types") do
      if ((entry.getObjVal? "schema").bind (·.getObjValAs? String "typeFingerprint")).toOption == some compiled.fingerprint then
        match entry.getObjValAs? String "id" with
        | .ok id => return "Aggregate:" ++ id
        | .error _ => fail span "invalid typed control schema identity"
    fail span "typed witness result schema is absent from control plan"

private def inputBindings (program : Program) (plan : Json) (entry : Export) : Except Diagnostic Json := do
  let some declaration := program.declarations.find? (·.id == entry.target)
    | fail entry.span "missing witness entry declaration"
  let mut scalarInputs := entry.inputs
  let mut aggregateInputs := entry.compositeInputs
  let mut bindings := []
  for parameter in declaration.parameters do
    let (name, type, names) ← match declaration.parameterType parameter with
      | .scalar _ => do
        let some input := scalarInputs.head? | fail entry.span "witness source input mismatch"
        scalarInputs := scalarInputs.drop 1
        pure (input.name, ResultType.scalar input.ty, [input.name])
      | .composite _ => do
        let some input := aggregateInputs.head? | fail entry.span "witness source input mismatch"
        aggregateInputs := aggregateInputs.drop 1
        let compiled ← (Types.compileType program.composites input.type).mapError fun diagnostic =>
          {span := input.span, message := diagnostic.message}
        let names := (Helpers.sourceLeafPaths compiled.checked.value "").map fun path => input.name ++ path
        pure (input.name, ResultType.composite input.type, names)
      | .unit => fail entry.span "witness source parameters cannot be Unit"
    bindings := bindings ++ [Json.mkObj [("name", toJson name),
      ("type", toJson (← resultToken program plan entry.span type)), ("inputs", toJson names)]]
  pure (toJson bindings)

structure Compiled where
  circuit : Circuit
  plan : Json
  binding : Json

private def boundedNativePlan (plan binding : Json) : Except Diagnostic Json := do
  let text := binding.compress ++ "\n"
  if text.utf8ByteSize > 524288 then fail {} "witness binding exceeds byte limit"
  let plan ← setField plan "mode" (toJson ("native" : String))
  let plan ← setField plan "binding" (toJson text)
  if plan.compress.utf8ByteSize > 1048576 then fail {} "bound witness plan exceeds byte limit"
  pure plan

/-- The native workflow requires declared providers and an exact ordered map
from executed calls to actual fresh private inputs. Host-only control is separate. -/
def compileWithLimits (limits : Helpers.Limits) (program : Program) (entryName : String)
    (circuitName : String := "") (outputName : String := "") : Except Diagnostic Compiled := do
  let plan ← Control.compileTypedWithLimits limits program entryName
  let some entry := program.exports.find? (·.name == entryName) | fail {} "unknown witness entrypoint"
  let lowered ← Helpers.compileHostedWithLimits limits (eraseProgram program) entryName
  let mut circuit := if circuitName.isEmpty then lowered.circuit else {lowered.circuit with name := circuitName}
  unless outputName.isEmpty do
    let some declaration := program.declarations.find? (·.id == entry.target)
      | fail entry.span "missing witness entry declaration"
    unless (match declaration.result with | .scalar _ => true | _ => false) do
      fail entry.span "named witness outputs require one scalar result"
    let [output] := circuit.outputs | fail entry.span "named witness outputs require one scalar result"
    if circuit.inputs.any (·.name == outputName) then
      fail entry.span "witness output name collides with an input"
    circuit := {circuit with outputs := [{output with name := outputName}]}
  let native ← Backend.Zkir.lowerCircuit circuit
  let mut calls := []
  for call in lowered.calls do
    calls := calls ++ [Json.mkObj [("ordinal", toJson (toString call.ordinal)), ("site", toJson call.site),
      ("name", toJson call.name), ("path", toJson (call.path.map idName)),
      ("resultType", toJson (← resultToken program plan entry.span call.result)), ("inputs", toJson call.inputs)]]
  let binding := Json.mkObj [("schemaVersion", toJson (1 : Nat)),
    ("kind", toJson ("typed-witness-bindings" : String)), ("circuitName", toJson circuit.name),
    ("sourceExport", toJson entryName), ("target", Json.mkObj [("kind", toJson ("standalone" : String))]),
    ("types", toJson (← arrayField plan "types")), ("signatures", toJson (← arrayField plan "witnesses")),
    ("inputBindings", ← inputBindings program plan entry),
    ("circuitInputs", toJson (circuit.inputs.map fun input => Json.mkObj [("name", toJson input.name),
      ("type", toJson (scalarName input.ty)), ("visibility", toJson (if input.visibility == .public then "public" else "private"))])),
    ("circuitOutputs", toJson (circuit.outputs.map fun output => Json.mkObj [("name", toJson output.name),
      ("type", toJson (scalarName output.ty))])),
    ("calls", toJson calls), ("nativeRelation", native)]
  pure {circuit, binding, plan := ← boundedNativePlan plan binding}

def compile (program : Program) (entryName : String) (circuitName : String := "")
    (outputName : String := "") : Except Diagnostic Compiled :=
  compileWithLimits {} program entryName circuitName outputName

/-- Bind the same source invocation to the actual ledger call relation, rather
than substituting the standalone relation's public-return convention. -/
def bindEntrypoint (compiled : Compiled) (relation : Json) (contractName entrypoint nativeCircuitFile targetProfile : String)
    (ledgerInputs : List (String × Ty) := []) :
    Except Diagnostic Compiled := do
  let mut binding ← setField compiled.binding "nativeRelation" relation
  unless ledgerInputs.isEmpty do
    for (_, ty) in ledgerInputs do
      if ty.isBytes || ty.isJubjub then
        fail {} "ledger witness bindings require scalar read components"
    binding ← setField binding "ledgerInputs" (toJson (ledgerInputs.map fun (name, ty) =>
      Json.mkObj [("name", toJson name), ("type", toJson (scalarName ty)),
        ("visibility", toJson ("public" : String))]))
  binding ← setField binding "target" (Json.mkObj [("kind", toJson ("entrypoint" : String)),
    ("contractName", toJson contractName), ("entrypoint", toJson entrypoint),
    ("nativeCircuitFile", toJson nativeCircuitFile), ("targetProfile", toJson targetProfile)])
  pure {compiled with binding, plan := ← boundedNativePlan compiled.plan binding}

end Noctium.Witness
