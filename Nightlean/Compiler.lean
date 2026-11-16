import Nightlean.Frontend
import Nightlean.Backend.Zkir
import Nightlean.Backend.Compact
import Nightlean.Target

namespace Nightlean.Compiler
open Lean Elab Command

private def sourceCapabilities : Capabilities :=
  { poseidon2 := Bool.true, stateCells := Bool.true, stateMaps := Bool.true }

private def typeName : Ty → String
  | .native => "Native"
  | .bool => "Bool"

private def expressionJson : Expr ty → Json
  | .native n => Json.mkObj [("native", toJson (toString n))]
  | .bool b => Json.mkObj [("bool", toJson b)]
  | .ref name => Json.mkObj [("ref", toJson name)]
  | .add a b => Json.mkObj [("add", toJson [expressionJson a, expressionJson b])]
  | .mul a b => Json.mkObj [("mul", toJson [expressionJson a, expressionJson b])]
  | .eq a b => Json.mkObj [("eq", toJson [expressionJson a, expressionJson b])]
  | .select c a b => Json.mkObj [("select", toJson [expressionJson c, expressionJson a, expressionJson b])]
  | .poseidon2 domain a b => Json.mkObj [("poseidon2", Json.mkObj [
      ("domain", toJson (toString domain)), ("args", toJson [expressionJson a, expressionJson b])])]

private def effectJson : Effect → Json
  | .readCell state destination ty => Json.mkObj [("op", toJson ("readCell" : String)),
      ("state", toJson state), ("destination", toJson destination), ("type", toJson (typeName ty))]
  | .readMap state destination _ ty key => Json.mkObj [("op", toJson ("readMap" : String)),
      ("state", toJson state), ("destination", toJson destination), ("type", toJson (typeName ty)),
      ("key", expressionJson key)]
  | .require condition => Json.mkObj [("op", toJson ("require" : String)), ("condition", expressionJson condition)]
  | .writeCell state _ value => Json.mkObj [("op", toJson ("writeCell" : String)),
      ("state", toJson state), ("value", expressionJson value)]
  | .writeMap state _ _ key value => Json.mkObj [("op", toJson ("writeMap" : String)),
      ("state", toJson state), ("key", expressionJson key), ("value", expressionJson value)]
  | .requireAbsent state _ key => Json.mkObj [("op", toJson ("requireAbsent" : String)),
      ("state", toJson state), ("key", expressionJson key)]

private def stateJson (state : StateDecl) : Json :=
  let kind := match state.kind with
    | .cell ty => Json.mkObj [("cell", toJson (typeName ty))]
    | .map kt vt => Json.mkObj [("map", toJson [typeName kt, typeName vt])]
  Json.mkObj [("name", toJson state.name), ("kind", kind)]

private def circuitSchemaJson (name : Name) (circuit : Circuit) : Json :=
  Json.mkObj [("name", toJson name.toString), ("file", toJson (name.toString ++ ".zkir")),
    ("inputs", toJson (circuit.inputs.map fun input => Json.mkObj [
      ("name", toJson input.name), ("type", toJson (typeName input.ty)),
      ("visibility", toJson (if input.visibility == .«public» then "public" else "private"))])),
    ("outputs", toJson (circuit.outputs.map fun out => Json.mkObj [
      ("name", toJson out.name), ("type", toJson (typeName out.ty)),
      ("visibility", toJson ("public" : String))]))]

private def failDiagnostic (d : Diagnostic) : CommandElabM α :=
  throwError "{d.span.file}:{d.span.line}:{d.span.column}: {d.message}"

/-- Evaluate only definitions generated and registered by the Nightlean elaborators. -/
private unsafe def registeredCircuits : CommandElabM (Array (Name × Circuit)) := do
  let env ← getEnv
  let mut circuits := #[]
  for info in circuitRegistry.getState env do
    unless env.isImportedConst info.declName do
      let circuit ← evalConstCheck Circuit ``Circuit info.declName
      match circuit.validate sourceCapabilities with
      | .error d => failDiagnostic d
      | .ok _ => circuits := circuits.push (info.declName, circuit)
  return circuits

private unsafe def registeredContracts : CommandElabM (Array (Name × Contract)) := do
  let env ← getEnv
  let mut contracts := #[]
  for name in contractRegistry.getState env do
    unless env.isImportedConst name do
      let contract ← evalConstCheck Contract ``Contract name
      match contract.validate sourceCapabilities with
      | .error d => failDiagnostic d
      | .ok _ => contracts := contracts.push (name, contract)
  return contracts

private def artifactName (name : Name) : String := name.toString

private def validateArtifactName (name : Name) : CommandElabM Unit := do
  let text := artifactName name
  if text.contains '/' || text.contains '\\' || (text.splitOn "..").length > 1 then
    throwError "circuit declaration name is not a safe artifact filename: {name}"

private unsafe def inspect : CommandElabM (Array (Name × Circuit) × Array (Name × Contract)) := do
  if (← get).messages.hasErrors then
    throwError "cannot export Nightlean artifacts after source elaboration errors"
  let circuits ← registeredCircuits
  let contracts ← registeredContracts
  if circuits.isEmpty then throwError "source contains no Nightlean circuit declarations"
  for (name, _) in circuits do validateArtifactName name
  for (name, contract) in contracts do
    validateArtifactName name
    for ep in contract.entrypoints do
      unless circuits.any (fun (_, circuit) => circuit.name == ep.circuit.name) do
        throwError "contract entrypoint references imported circuit '{ep.circuit.name}'; include its source declaration in this compilation unit"
  return (circuits, contracts)

elab "#nightlean_check" : command => do
  let (circuits, contracts) ← unsafe inspect
  logInfo m!"checked {circuits.size} circuit(s), {contracts.size} contract(s); target integration unqualified"

private def compileArtifacts (directory : String) (withCompact : _root_.Bool) : CommandElabM Unit := do
  let (circuits, contracts) ← unsafe inspect
  -- Lower everything before creating output files. Unsupported circuits cannot leave partial output.
  let mut lowered := #[]
  for (name, circuit) in circuits do
    match Backend.Zkir.lowerCircuit circuit with
    | .error d => failDiagnostic d
    | .ok json => lowered := lowered.push (artifactName name ++ ".zkir", json.pretty)
  if withCompact && contracts.isEmpty then
    throwError "Compact adapter requires a Nightlean contract declaration"
  if withCompact then
    for (name, contract) in contracts do
      match Backend.Compact.emit contract with
      | .error message => throwError "Compact adapter: {message}"
      | .ok source => lowered := lowered.push (artifactName name ++ ".compact", source)
  let contractMetadata := contracts.map fun (name, contract) => Json.mkObj [
    ("name", toJson name.toString),
    ("state", toJson (contract.state.map stateJson)),
    ("entrypoints", toJson (contract.entrypoints.map fun ep => Json.mkObj [
      ("name", toJson ep.name), ("circuit", toJson ep.circuit.name),
      ("effects", toJson (ep.effects.map effectJson))]))]
  let adapterBindings := if withCompact then contracts.map fun (name, contract) =>
    Json.mkObj [("contract", toJson name.toString),
      ("source", toJson (artifactName name ++ ".compact")),
      ("witnesses", toJson ((Backend.Compact.witnessBindings contract).map fun binding =>
        Json.mkObj [("entrypoint", toJson binding.entrypoint),
          ("input", toJson binding.inputName), ("provider", toJson binding.providerName),
          ("type", toJson (typeName binding.ty))]))]
    else #[]
  let metadata := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("target", toJson ("midnight-ledger-9" : String)),
    ("targetProfile", toJson TargetProfile.sourceBaseline),
    ("qualification", toJson ("unqualified-relation-and-state-description" : String)),
    ("deployable", toJson Bool.false),
    ("adapter", if withCompact then toJson ("compact-source" : String) else Json.null),
    ("adapterBindings", Json.arr adapterBindings),
    ("contracts", Json.arr contractMetadata),
    ("circuits", toJson (circuits.map fun (name, circuit) => circuitSchemaJson name circuit))]
  let path : System.FilePath := directory
  liftIO <| IO.FS.createDirAll path
  for (name, content) in lowered do
    liftIO <| IO.FS.writeFile (path / name) (content ++ "\n")
  liftIO <| IO.FS.writeFile (path / "nightlean.json") (metadata.pretty ++ "\n")
  logInfo m!"emitted {circuits.size} relation(s) and state metadata to {path}; not a deployable contract bundle"

elab "#nightlean_compile" directory:str : command =>
  compileArtifacts directory.getString Bool.false

elab "#nightlean_compile_compact" directory:str : command =>
  compileArtifacts directory.getString Bool.true

end Nightlean.Compiler
