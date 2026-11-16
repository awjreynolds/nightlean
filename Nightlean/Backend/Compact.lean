import Nightlean.IR

namespace Nightlean.Backend.Compact

structure WitnessBinding where
  entrypoint : String
  inputName : String
  providerName : String
  ty : Ty
  deriving Repr

def witnessBindings (contract : Contract) : List WitnessBinding :=
  contract.entrypoints.flatMap fun entry =>
    (entry.circuit.inputs.filter (·.visibility == .«private»)).map fun input =>
      {entrypoint := entry.name, inputName := input.name,
       providerName := "w_" ++ entry.name ++ "_" ++ input.name, ty := input.ty}

private def typeName : Ty → String
  | .native => "Field"
  | .bool => "Boolean"

private def reserved : List String := ["assert", "as", "Boolean", "Bytes", "circuit", "const",
  "constructor", "Counter", "default", "disclose", "else", "enum", "export", "Field", "for",
  "if", "import", "ledger", "Map", "module", "new", "opaque", "pad", "pragma", "return",
  "Set", "struct", "transientHash", "true", "false", "Uint", "Vector", "witness",
  "let", "type", "pure", "sealed", "include", "of", "where", "end", "fold", "map"]

private def identifier (name : String) : Except String Unit := do
  let chars := name.toList
  let some first := chars.head? | throw "empty Compact identifier"
  unless first.isAlpha && first.toNat < 128 || first == '_' do
    throw s!"invalid Compact identifier '{name}'"
  unless chars.all (fun c => (c.isAlphanum && c.toNat < 128) || c == '_') do
    throw s!"invalid Compact identifier '{name}'"
  if reserved.contains name then throw s!"reserved Compact identifier '{name}'"
  if name.startsWith "nl_" || name.startsWith "w_" || name.startsWith "init_" then
    throw s!"Compact identifier '{name}' uses a generated-name prefix"

private structure LowerState where
  next : Nat := 0
  lines : List String := []
  cache : List (String × String) := []

private abbrev LowerM := StateT LowerState (Except String)

private def line (source : String) : LowerM Unit :=
  modify fun s => {s with lines := s.lines ++ ["  " ++ source]}

private def fresh : LowerM String := do
  let s ← get
  set {s with next := s.next + 1}
  pure s!"nl_v{s.next}"

private def cached (key : String) (make : LowerM String) : LowerM String := do
  if let some value := (← get).cache.lookup key then return value
  let value ← make
  modify fun s => {s with cache := (key, value) :: s.cache}
  pure value

private def lowerExpr (env : List (String × String)) (expr : Expr ty) : LowerM String :=
  cached (reprStr expr) do
    match (dependent := true) expr with
    | .native n => pure s!"({n} as Field)"
    | .bool b => pure (if b then "true" else "false")
    | .ref name =>
      match env.lookup name with
      | some target => pure target
      | none => throw s!"unbound Compact expression '{name}'"
    | .add a b => do
      let a ← lowerExpr env a
      let b ← lowerExpr env b
      let name ← fresh
      line s!"const {name} = {a} + {b};"
      pure name
    | .mul a b => do
      let a ← lowerExpr env a
      let b ← lowerExpr env b
      let name ← fresh
      line s!"const {name} = {a} * {b};"
      pure name
    | .eq a b => do
      let a ← lowerExpr env a
      let b ← lowerExpr env b
      let name ← fresh
      line s!"const {name} = {a} == {b};"
      pure name
    | .select condition yes no => do
      let condition ← lowerExpr env condition
      let yes ← lowerExpr env yes
      let no ← lowerExpr env no
      let name ← fresh
      line s!"const {name} = {condition} ? {yes} : {no};"
      pure name
    | .poseidon2 domain a b => do
      let a ← lowerExpr env a
      let b ← lowerExpr env b
      let name ← fresh
      line s!"const {name} = transientHash<Vector<3, Field>>([{domain} as Field, {a}, {b}]);"
      pure name
termination_by sizeOf expr

private def emitEntry (entry : Entrypoint) : Except String String := do
  let publicInputs := entry.circuit.inputs.filter (·.visibility == .«public»)
  let params := publicInputs.map fun input => s!"nl_arg_{input.name}: {typeName input.ty}"
  let outputTypes := entry.circuit.outputs.map fun output => typeName output.ty
  let body : LowerM Unit := do
    let mut env : List (String × String) := []
    for input in entry.circuit.inputs do
      let target := s!"nl_input_{input.name}"
      let value := if input.visibility == .«public» then s!"disclose(nl_arg_{input.name})"
        else s!"w_{entry.name}_{input.name}()"
      line s!"const {target} = {value};"
      env := (input.name, target) :: env
    for constraint in entry.circuit.constraints do
      line s!"assert({← lowerExpr env constraint}, \"Nightlean circuit constraint\");"
    let mut publicEnv : List (String × String) := publicInputs.map fun input =>
      (input.name, s!"nl_input_{input.name}")
    let mut returns : List String := []
    for output in entry.circuit.outputs do
      let value ← lowerExpr env output.value
      let target := s!"nl_output_{output.name}"
      line s!"const {target} = disclose({value});"
      publicEnv := (output.name, target) :: publicEnv
      returns := returns ++ [target]
    -- Cache keys refer to syntax names. Clear at the relation/state boundary,
    -- where only public values and explicit state reads are in scope.
    modify fun s => {s with cache := []}
    for effect in entry.effects do
      match effect with
      | .readCell state destination _ =>
        let target := s!"nl_read_{destination}"
        line s!"const {target} = {state};"
        publicEnv := (destination, target) :: publicEnv
      | .readMap .. => throw "Compact adapter does not yet qualify map reads"
      | .require condition =>
        line s!"assert({← lowerExpr publicEnv condition}, \"Nightlean state guard\");"
      | .writeCell state _ value =>
        line s!"{state} = disclose({← lowerExpr publicEnv value});"
      | .writeMap state _ _ key value =>
        line s!"{state}.insert(disclose({← lowerExpr publicEnv key}), disclose({← lowerExpr publicEnv value}));"
      | .requireAbsent state _ key =>
        line s!"assert(!{state}.member(disclose({← lowerExpr publicEnv key})), \"Nightlean map key already spent\");"
    line ("return [" ++ String.intercalate ", " returns ++ "];")
  let (_, state) ← body.run {}
  pure ("export circuit " ++ entry.name ++ "(" ++ String.intercalate ", " params ++
    "): [" ++ String.intercalate ", " outputTypes ++ "] {\n" ++ String.intercalate "\n" state.lines ++ "\n}\n")

/-- Optional packaging source. It does not replace the primary Lean ZKIR emitter.
Only this adapter's finite typed mapping is supported. -/
def emit (contract : Contract) : Except String String := do
  match contract.validate {poseidon2 := true, stateCells := true, stateMaps := true} with
  | .error diagnostic => throw diagnostic.message
  | .ok _ => pure ()
  identifier contract.name
  for state in contract.state do identifier state.name
  for entry in contract.entrypoints do
    identifier entry.name
    for input in entry.circuit.inputs do identifier input.name
    for output in entry.circuit.outputs do identifier output.name
    for effect in entry.effects do
      match effect with
      | .readCell _ destination _ | .readMap _ destination .. => identifier destination
      | _ => pure ()
  let bindings := witnessBindings contract
  let globalNames := contract.state.map (·.name) ++ contract.entrypoints.map (·.name) ++
    bindings.map (·.providerName)
  if !uniqueNames globalNames then throw "Compact global declaration name collision"
  if !uniqueNames (bindings.map (·.providerName)) then throw "ambiguous Compact witness provider names"
  let mut sections := ["pragma language_version >= 0.28.0;\n\nimport CompactStandardLibrary;\n"]
  for state in contract.state do
    let ty := match state.kind with
      | .cell ty => typeName ty
      | .map key value => s!"Map<{typeName key}, {typeName value}>"
    sections := sections ++ [s!"export ledger {state.name}: {ty};"]
  for binding in bindings do
    sections := sections ++ [s!"witness {binding.providerName}(): {typeName binding.ty};"]
  let cells := contract.state.filter fun state => match state.kind with | .cell _ => true | _ => false
  if !cells.isEmpty then
    let params := cells.map fun state => match state.kind with
      | .cell ty => s!"init_{state.name}: {typeName ty}"
      | _ => ""
    let assignments := cells.map fun state => s!"  {state.name} = disclose(init_{state.name});"
    sections := sections ++ ["constructor(" ++ String.intercalate ", " params ++ ") {\n" ++
      String.intercalate "\n" assignments ++ "\n}"]
  for entry in contract.entrypoints do
    sections := sections ++ [← emitEntry entry]
  pure (String.intercalate "\n\n" sections ++ "\n")

end Nightlean.Backend.Compact
