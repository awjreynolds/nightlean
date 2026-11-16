import Nightlean.Frontend
import Nightlean.Backend.Zkir
import Nightlean.Target

namespace Nightlean.Compiler
open Lean Elab Command

private def sourceCapabilities : Capabilities :=
  { poseidon2 := Bool.true, stateCells := Bool.true, stateMaps := Bool.true }

private def typeName : Ty → String
  | .native => "Native"
  | .bool => "Bool"
  | .uint maximum => s!"UIntRange<{maximum + 1}>"

private def expressionJson : Expr ty → Json
  | .native n => Json.mkObj [("native", toJson (toString n))]
  | .bool b => Json.mkObj [("bool", toJson b)]
  | .uint maximum value => Json.mkObj [("uint", Json.mkObj [
      ("maximum", toJson (toString maximum)), ("value", toJson (toString value))])]
  | .ref name => Json.mkObj [("ref", toJson name)]
  | .add a b => Json.mkObj [("add", toJson [expressionJson a, expressionJson b])]
  | .mul a b => Json.mkObj [("mul", toJson [expressionJson a, expressionJson b])]
  | .sub a b => Json.mkObj [("sub", toJson [expressionJson a, expressionJson b])]
  | .uadd a b => Json.mkObj [("uadd", toJson [expressionJson a, expressionJson b])]
  | .usub a b => Json.mkObj [("usub", toJson [expressionJson a, expressionJson b])]
  | .umul a b => Json.mkObj [("umul", toJson [expressionJson a, expressionJson b])]
  | .cast target value => Json.mkObj [("cast", Json.mkObj [
      ("type", toJson (typeName target)), ("value", expressionJson value)])]
  | .letE name value body => Json.mkObj [("let", Json.mkObj [
      ("name", toJson name), ("value", expressionJson value), ("body", expressionJson body)])]
  | .assertE condition body => Json.mkObj [("assertThen", toJson [expressionJson condition, expressionJson body])]
  | .disclose _ value => expressionJson value
  | .eq a b => Json.mkObj [("eq", toJson [expressionJson a, expressionJson b])]
  | .select c a b => Json.mkObj [("select", toJson [expressionJson c, expressionJson a, expressionJson b])]
  | .poseidon2 domain a b => Json.mkObj [("poseidon2", Json.mkObj [
      ("domain", toJson (toString domain)), ("args", toJson [expressionJson a, expressionJson b])])]

/-- Symbolic source expressions for the native runtime. Values are AST constants or references,
never an execution witness. Decimal field constants avoid JavaScript number truncation. -/
private def nativeExpressionJson : Expr ty → Json
  | .native n => Json.mkObj [("tag", toJson ("constant" : String)), ("value", toJson (toString n))]
  | .bool b => Json.mkObj [("tag", toJson ("bool" : String)), ("value", toJson b)]
  | .uint maximum value => Json.mkObj [("tag", toJson ("uint" : String)),
      ("maximum", toJson (toString maximum)), ("value", toJson (toString value))]
  | .ref name => Json.mkObj [("tag", toJson ("reference" : String)), ("name", toJson name)]
  | .add a b => binary "add" (nativeExpressionJson a) (nativeExpressionJson b)
  | .mul a b => binary "mul" (nativeExpressionJson a) (nativeExpressionJson b)
  | .sub a b => binary "sub" (nativeExpressionJson a) (nativeExpressionJson b)
  | .uadd (m := m) (n := n) a b => unsigned "uadd" (m + n) (nativeExpressionJson a) (nativeExpressionJson b)
  | .usub (m := m) a b => unsigned "usub" m (nativeExpressionJson a) (nativeExpressionJson b)
  | .umul (m := m) (n := n) a b => unsigned "umul" (m * n) (nativeExpressionJson a) (nativeExpressionJson b)
  | .cast target value => Json.mkObj [("tag", toJson ("cast" : String)),
      ("type", toJson (typeName target)), ("value", nativeExpressionJson value)]
  | .letE name value body => Json.mkObj [("tag", toJson ("let" : String)),
      ("name", toJson name), ("value", nativeExpressionJson value), ("body", nativeExpressionJson body)]
  | .assertE condition body => Json.mkObj [("tag", toJson ("assertThen" : String)),
      ("condition", nativeExpressionJson condition), ("body", nativeExpressionJson body)]
  | .disclose _ value => nativeExpressionJson value
  | .eq a b => binary "eq" (nativeExpressionJson a) (nativeExpressionJson b)
  | .select c a b => Json.mkObj [("tag", toJson ("select" : String)),
      ("condition", nativeExpressionJson c), ("yes", nativeExpressionJson a), ("no", nativeExpressionJson b)]
  | .poseidon2 domain a b => Json.mkObj [("tag", toJson ("poseidon2" : String)),
      ("domain", toJson (toString domain)), ("left", nativeExpressionJson a), ("right", nativeExpressionJson b)]
where
  binary (tag : String) (left right : Json) : Json :=
    Json.mkObj [("tag", toJson tag), ("left", left), ("right", right)]
  unsigned (tag : String) (maximum : Nat) (left right : Json) : Json :=
    Json.mkObj [("tag", toJson tag), ("maximum", toJson (toString maximum)),
      ("left", left), ("right", right)]

private def alignedJson (value : Backend.Impact.Aligned) : List (String × Json) :=
  match value with
  | .field expression => [("alignment", toJson ("field" : String)), ("expression", nativeExpressionJson expression)]
  | .bit b => [("alignment", toJson ("bit" : String)), ("expression", nativeExpressionJson (.bool b))]

private def operationJson : Backend.Impact.Op → Json
  | .dup => Json.mkObj [("op", toJson ("dup" : String))]
  | .index slot pushPath => Json.mkObj [("op", toJson ("index" : String)),
      ("slot", toJson slot), ("pushPath", toJson pushPath)]
  | .push value storage => Json.mkObj ([("op", toJson ("push" : String)), ("storage", toJson storage)] ++ alignedJson value)
  | .popeq value => Json.mkObj ([("op", toJson ("popeq" : String))] ++ alignedJson value)
  | .member => Json.mkObj [("op", toJson ("member" : String))]
  | .insert n => Json.mkObj [("op", toJson ("insert" : String)), ("n", toJson n)]

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
      ("visibility", toJson ("public" : String)), ("expression", nativeExpressionJson out.value)])),
    ("constraints", toJson (circuit.constraints.map nativeExpressionJson))]

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
      | .ok _ =>
        match Disclosure.circuit circuit with
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
      | .ok _ =>
        match Disclosure.contract contract with
        | .error d => failDiagnostic d
        | .ok _ => contracts := contracts.push (name, contract)
  return contracts

private def artifactName (name : Name) : String := name.toString

private def validateArtifactStem (text : String) : CommandElabM Unit := do
  if text.contains '/' || text.contains '\\' || (text.splitOn "..").length > 1 then
    throwError "declaration name is not a safe artifact filename: {text}"

private def validateArtifactName (name : Name) : CommandElabM Unit :=
  validateArtifactStem (artifactName name)

private def nativeCircuitFile (contract : Name) (ep : Entrypoint) : String :=
  artifactName contract ++ "." ++ ep.name ++ ".zkir"

private def nativePlanFile (contract : Name) (ep : Entrypoint) : String :=
  artifactName contract ++ "." ++ ep.name ++ ".impact.json"

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
      validateArtifactStem ep.name
      unless circuits.any (fun (_, circuit) => circuit.name == ep.circuit.name) do
        throwError "contract entrypoint references imported circuit '{ep.circuit.name}'; include its source declaration in this compilation unit"
  return (circuits, contracts)

elab "#nightlean_check" : command => do
  let (circuits, contracts) ← unsafe inspect
  logInfo m!"checked {circuits.size} circuit(s), {contracts.size} contract(s); target integration unqualified"

private unsafe def checkTarget (profile : TargetProfile) : CommandElabM Unit := do
  let (circuits, contracts) ← unsafe inspect
  logInfo m!"checked {circuits.size} circuit(s), {contracts.size} contract(s); target {profile.name} ({profile.qualification})"

private def parseTargetProfile (source : String) : CommandElabM TargetProfile := do
  match TargetProfile.parse source with
  | .ok profile => pure profile
  | .error message => throwError "invalid target profile: {message}"

elab "#nightlean_check_target" profileJson:str : command => do
  let profile ← parseTargetProfile profileJson.getString
  unsafe checkTarget profile

private def compileArtifacts (directory : String) (profile : TargetProfile) : CommandElabM Unit := do
  let (circuits, contracts) ← unsafe inspect
  -- Lower everything before creating output files. Unsupported circuits cannot leave partial output.
  let mut lowered := #[]
  for (name, circuit) in circuits do
    match Backend.Zkir.lowerCircuit circuit with
    | .error d => failDiagnostic d
    | .ok json => lowered := lowered.push (artifactName name ++ ".zkir", json.pretty)
  for (name, contract) in contracts do
    for ep in contract.entrypoints do
      let ep := Passes.pruneEntrypoint ep
      match Backend.Zkir.lowerEntrypoint contract.state ep with
      | .error d => failDiagnostic d
      | .ok json => lowered := lowered.push (nativeCircuitFile name ep, json.pretty)
      let plan ← match Backend.Impact.lower contract.state ep with
        | .error d => failDiagnostic d
        | .ok plan => pure plan
      let targetPlanFields := if profile.name == TargetProfile.selected321.name then [
        ("target", toJson profile.name), ("targetProfile", toJson profile)
      ] else []
      let planJson := Json.mkObj ([
        ("schemaVersion", toJson (1 : Nat))] ++ targetPlanFields ++ [
        ("contractName", toJson name.toString),
        ("entrypoint", toJson ep.name), ("nativeCircuitFile", toJson (nativeCircuitFile name ep)),
        ("state", toJson (contract.state.map stateJson)),
        ("circuit", circuitSchemaJson ep.circuit.name.toName ep.circuit),
        ("operations", toJson (plan.operations.map operationJson)),
        ("reads", toJson (plan.reads.map fun item => Json.mkObj [
          ("name", toJson item.name), ("type", toJson (typeName item.ty))])),
        ("guards", toJson (plan.guards.map nativeExpressionJson))])
      lowered := lowered.push (nativePlanFile name ep, planJson.pretty)
  unless uniqueNames (lowered.toList.map (·.1)) do
    throwError "generated artifact filenames collide; rename the circuit or contract entrypoint"
  let contractMetadata := contracts.map fun (name, contract) => Json.mkObj [
    ("name", toJson name.toString),
    ("state", toJson (contract.state.map stateJson)),
    ("entrypoints", toJson (contract.entrypoints.map fun ep => Json.mkObj [
      ("name", toJson ep.name), ("circuit", toJson ep.circuit.name),
      ("nativeCircuitFile", toJson (nativeCircuitFile name ep)),
      ("nativePlanFile", toJson (nativePlanFile name ep)),
      ("nativeCircuitQualified", toJson Bool.false),
      ("effects", toJson (ep.effects.map effectJson))]))]
  let metadata := Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)), ("target", toJson profile.name),
    ("targetProfile", toJson profile),
    ("qualification", toJson ("unqualified-relation-and-state-description" : String)),
    ("deployable", toJson Bool.false),
    ("contracts", Json.arr contractMetadata),
    ("circuits", toJson (circuits.map fun (name, circuit) => circuitSchemaJson name circuit))]
  let path : System.FilePath := directory
  liftIO <| IO.FS.createDirAll path
  for (name, content) in lowered do
    liftIO <| IO.FS.writeFile (path / name) (content ++ "\n")
  liftIO <| IO.FS.writeFile (path / "nightlean.json") (metadata.pretty ++ "\n")
  let nativeCount : Nat := contracts.foldl (fun total (_, contract) => total + contract.entrypoints.length) 0
  logInfo m!"emitted {circuits.size} circuit relation(s), {nativeCount} native entrypoint relation(s), and state metadata to {path}; not a deployable contract bundle"

elab "#nightlean_compile" directory:str : command =>
  compileArtifacts directory.getString TargetProfile.sourceBaseline

elab "#nightlean_compile_target" directory:str profileJson:str : command => do
  let profile ← parseTargetProfile profileJson.getString
  compileArtifacts directory.getString profile

end Nightlean.Compiler
