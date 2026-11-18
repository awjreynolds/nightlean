import Noctium.Backend.Impact
import Noctium.Backend.NativeMeaning

namespace Noctium.Backend.Native

private def hashCapabilities : Capabilities :=
  {poseidon2 := true, persistentHash32 := true, persistentHashVector32 := true,
    persistentHashNative := true, bytes32Conversions := true, sha512 := true, keccak256 := true, typedBoolean := true, hashToCurve := true, foreignValues := true, jubjub := true}

private def inputRequirement (input : Input) : InputRequirement :=
  {identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}

private def inputAliases (inputs : List InputRequirement) : AliasEnvironment :=
  inputs.map fun input => (input.identifier.drop 7 |>.toString, .input input.identifier)

private def sourceInputAliases (inputs : List Input) : AliasEnvironment :=
  inputs.map fun input => (input.name, Input.sourceTerm input)

private def convert (span : SourceSpan) (result : Except String α) : Except Diagnostic α :=
  match result with
  | .ok value => .ok value
  | .error message => .error {span, message}

private def collect (env : AliasEnvironment) (values : List (Expr ty)) : Except String (List Term × List (Term × Nat) × List Term) := do
  let results ← values.mapM (normalize env)
  pure (results.map (·.term), results.flatMap (·.bounds), results.flatMap (·.assertions))

theorem inputRequirement_eq (input : Input) :
    inputRequirement input =
      {identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty} := rfl

theorem inputRequirement_function_eq :
    inputRequirement = (fun input : Input =>
      ({identifier := "%input_" ++ input.name,
        visibility := input.visibility, ty := input.ty} : InputRequirement)) := rfl

theorem convert_eq_mapError (span : SourceSpan) (result : Except String α) :
    convert span result = result.mapError (fun message => {span, message}) := by
  cases result <;> rfl

theorem inputAliases_eq (inputs : List InputRequirement) :
    inputAliases inputs = inputs.map (fun input => (input.identifier.drop 7 |>.toString, .input input.identifier)) := rfl

theorem inputAliases_source (inputs : List Input) :
    inputAliases (inputs.map inputRequirement) =
      inputs.map (fun input => (input.name, Term.input ("%input_" ++ input.name))) := by
  have strip (name : String) : (("%input_" ++ name).drop 7).copy = name := by
    apply String.toList_injective
    change (("%input_" ++ name).drop 7).copy.toList = name.toList
    rw [String.toList_copy_drop, String.toList_append]
    rfl
  simp [inputAliases, inputRequirement, List.map_map, strip]

theorem sourceInputAliases_source (inputs : List Input) :
    sourceInputAliases inputs = inputs.map (fun input => (input.name, Input.sourceTerm input)) := rfl

theorem convert_ok (span : SourceSpan) (result : Except String α) (value : α) :
    convert span result = .ok value ↔ result = .ok value := by
  cases result <;> simp [convert]

theorem collect_eq (env : AliasEnvironment) (values : List (Expr ty)) :
    collect env values = (do
      let results ← values.mapM (normalize env)
      pure (results.map (·.term), results.flatMap (·.bounds), results.flatMap (·.assertions))) := rfl

/-- The exact production normalizer call for one Impact operation. -/
def collectOperation (span : SourceSpan) (aliases : AliasEnvironment)
    (operation : Impact.Op) :
    Except Diagnostic (List (List Term) × List (Term × Nat) × List Term) := do
  let pieces ← operation.fieldGroups.mapM fun fields =>
    convert span (collect aliases fields)
  pure (pieces.map (·.1), pieces.flatMap (·.2.1), pieces.flatMap (·.2.2))

/-- The production operation fold keeps each normalized Impact opcode in its
own ordered native public-input group. It also retains field bounds and nested
assertions in source order. -/
def collectOperations (span : SourceSpan) (aliases : AliasEnvironment)
    (operations : List Impact.Op) (initialBounds : List (Term × Nat)) :
    Except Diagnostic (List (List Term) × List (Term × Nat) × List Term) := do
  let pieces ← operations.mapM (collectOperation span aliases)
  pure (pieces.flatMap (fun piece => piece.1),
    initialBounds ++ pieces.flatMap (fun piece => piece.2.1),
    pieces.flatMap (fun piece => piece.2.2))

def expectedCircuit (value : Circuit) : Except Diagnostic Expected := do
  value.validate hashCapabilities
  Disclosure.circuit value
  let inputs := value.inputs.flatMap Input.requirements
  let aliases := sourceInputAliases value.inputs
  let (_, constraints, _) ← convert value.span (collect aliases value.constraints)
  let conditions ← convert value.span (value.constraints.mapM (normalize aliases))
  let mut outputs := []
  let mut emptyOutputs := []
  for output in value.outputs do
    if output.ty == .bytes 0 then
      emptyOutputs := emptyOutputs ++ [← convert output.span (normalize aliases output.value)]
    let fields ← convert output.span output.nativeReturnFields
    for field in fields do
      outputs := outputs ++ [← convert output.span (normalize aliases field)]
  let returns := outputs.map (·.term)
  let groups := (value.inputs.filter (·.visibility == .«public»)).flatMap fun input =>
    match input.ty with
    | .foreign kind => (List.range kind.encodedFieldCount).map fun index =>
        [foreignEncodedFieldTerm kind (Input.sourceTerm input) index]
    | _ => input.nativeIdentifiers.map fun identifier => [.input identifier]
  pure {
    mode := .relation
    inputs := inputs
    returns := returns
    assertions := conditions.flatMap (fun result => result.assertions ++ [result.term]) ++
      outputs.flatMap (·.assertions) ++ emptyOutputs.flatMap (·.assertions)
    groups := groups ++ (if returns.isEmpty then [] else [returns])
    bounds := constraints ++ outputs.flatMap (·.bounds) ++ emptyOutputs.flatMap (·.bounds)
  }

/-- Derive the schedule from source effects again, rather than trusting a raw
producer's alleged group count or supplied payload list. Impact layout and its
native ledger interpretation remain separately tested/proved obligations. -/
def expectedEntrypoint (state : List StateDecl) (value : Entrypoint) : Except Diagnostic Expected := do
  let plan ← Impact.lower state value
  let publicCount := Impact.publicInputReadCount value.circuit.inputs
  let circuitInputs := value.circuit.inputs.flatMap Input.requirements
  let readInputs := (plan.reads.drop publicCount).flatMap fun read =>
      read.bindings.map fun (name, ty) =>
        ({identifier := "%input_" ++ name, visibility := .«public», ty} : InputRequirement)
  let mut inputs := circuitInputs ++ readInputs
  let mut aliases := sourceInputAliases value.circuit.inputs ++ inputAliases readInputs
  let mut outputBounds := []
  let mut outputAssertions := []
  for output in value.circuit.outputs do
    let result ← convert output.span (normalize aliases output.value)
    aliases := (output.name, result.term) :: aliases
    outputBounds := outputBounds ++ result.bounds
    outputAssertions := outputAssertions ++ result.assertions
  let mut readAssertions := []
  let mut readBounds := []
  let mut readInputIndex := circuitInputs.length
  for read in plan.reads.drop publicCount do
    if let some guard := read.guard then
      let result ← convert value.span (normalize aliases guard)
      let start := readInputIndex
      let finish := start + read.bindings.length
      inputs := inputs.zipIdx.map fun (input, position) =>
        if start ≤ position && position < finish then
          {input with activityGuard := some result.term} else input
      readAssertions := readAssertions ++ result.assertions
      readBounds := readBounds ++ result.bounds
    for condition in read.inactiveDefaultConstraints do
      let result ← convert value.span (normalize aliases condition)
      readAssertions := readAssertions ++ result.assertions ++ [result.term]
      readBounds := readBounds ++ result.bounds
    readInputIndex := readInputIndex + read.bindings.length
  let (_, constraints, _) ← convert value.span (collect aliases value.circuit.constraints)
  let conditions ← convert value.span (value.circuit.constraints.mapM (normalize aliases))
  let (_, guards, _) ← convert value.span (collect aliases plan.guards)
  let guardConditions ← convert value.span (plan.guards.mapM (normalize aliases))
  let (groups, bounds, operationAssertions) ←
    collectOperations value.span aliases plan.operations outputBounds
  let mut returnResults := []
  let mut emptyReturns := []
  for output in value.returns do
    if output.ty == .bytes 0 then
      emptyReturns := emptyReturns ++ [← convert output.span (normalize aliases output.value)]
    let fields ← convert output.span output.nativeReturnFields
    for field in fields do
      returnResults := returnResults ++ [← convert output.span (normalize aliases field)]
  let returnedBounds := (returnResults ++ emptyReturns).flatMap (·.bounds)
  let returnedAssertions := (returnResults ++ emptyReturns).flatMap (·.assertions)
  let activityGuards := if plan.activityGuards.isEmpty then
      plan.operations.flatMap fun operation => List.replicate operation.fieldGroups.length none
    else
      plan.operations.zip plan.activityGuards |>.flatMap fun (operation, guard) =>
        List.replicate operation.fieldGroups.length guard
  let guardResults ← activityGuards.mapM fun guard => match guard with
    | none => pure ({term := .constant 1} : Normalized)
    | some guard => convert value.span (normalize aliases guard)
  pure {
    mode := .ledgerCall
    inputs := inputs
    groups := groups
    groupGuards := guardResults.map (·.term)
    returns := returnResults.map (·.term)
    assertions := conditions.flatMap (fun result => result.assertions ++ [result.term]) ++
      outputAssertions ++ readAssertions ++
      guardConditions.flatMap (fun result => result.assertions ++ [result.term]) ++
      operationAssertions ++ returnedAssertions ++ guardResults.flatMap (·.assertions)
    bounds := bounds ++ constraints ++ readBounds ++ guards ++ returnedBounds ++
      guardResults.flatMap (·.bounds)
  }

end Noctium.Backend.Native
