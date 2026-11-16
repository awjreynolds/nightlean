import Nightlean.Backend.Impact
import Nightlean.Backend.NativeMeaning

namespace Nightlean.Backend.Native

private def inputRequirement (input : Input) : InputRequirement :=
  {identifier := "%input_" ++ input.name, visibility := input.visibility, ty := input.ty}

private def inputAliases (inputs : List InputRequirement) : AliasEnvironment :=
  inputs.map fun input => (input.identifier.drop 7 |>.toString, .input input.identifier)

private def convert (span : SourceSpan) (result : Except String α) : Except Diagnostic α :=
  match result with
  | .ok value => .ok value
  | .error message => .error {span, message}

private def collect (env : AliasEnvironment) (values : List (Expr ty)) : Except String (List Term × List (Term × Nat) × List Term) := do
  let results ← values.mapM (normalize env)
  pure (results.map (·.term), results.flatMap (·.bounds), results.flatMap (·.assertions))

def expectedCircuit (value : Circuit) : Except Diagnostic Expected := do
  value.validate {poseidon2 := true}
  Disclosure.circuit value
  let inputs := value.inputs.map inputRequirement
  let aliases := inputAliases inputs
  let (_, constraints, _) ← convert value.span (collect aliases value.constraints)
  let conditions ← convert value.span (value.constraints.mapM (normalize aliases))
  let outputs ← value.outputs.mapM fun output => convert output.span (normalize aliases output.value)
  let returns := outputs.map (·.term)
  let groups := (inputs.filter (·.visibility == .«public»)).map (fun input => [.input input.identifier])
  pure {
    mode := .relation
    inputs := inputs
    returns := returns
    assertions := conditions.flatMap (fun result => result.assertions ++ [result.term]) ++
      outputs.flatMap (·.assertions)
    groups := groups ++ (if returns.isEmpty then [] else [returns])
    bounds := constraints ++ outputs.flatMap (·.bounds)
  }

/-- Derive the schedule from source effects again, rather than trusting a raw
producer's alleged group count or supplied payload list. Impact layout and its
native ledger interpretation remain separately tested/proved obligations. -/
def expectedEntrypoint (state : List StateDecl) (value : Entrypoint) : Except Diagnostic Expected := do
  let plan ← Impact.lower state value
  let publicCount := (value.circuit.inputs.filter (·.visibility == .«public»)).length
  let inputs := value.circuit.inputs.map inputRequirement ++
    (plan.reads.drop publicCount).map fun read =>
      {identifier := "%input_" ++ read.name, visibility := .«public», ty := read.ty}
  let mut aliases := inputAliases inputs
  let mut bounds := []
  let mut outputAssertions := []
  for output in value.circuit.outputs do
    let result ← convert output.span (normalize aliases output.value)
    aliases := (output.name, result.term) :: aliases
    bounds := bounds ++ result.bounds
    outputAssertions := outputAssertions ++ result.assertions
  let (_, constraints, _) ← convert value.span (collect aliases value.circuit.constraints)
  let conditions ← convert value.span (value.circuit.constraints.mapM (normalize aliases))
  let (_, guards, _) ← convert value.span (collect aliases plan.guards)
  let guardConditions ← convert value.span (plan.guards.mapM (normalize aliases))
  let mut operationAssertions := []
  let mut groups := []
  for operation in plan.operations do
    let (values, requirements, nestedAssertions) ← convert value.span (collect aliases operation.fields)
    operationAssertions := operationAssertions ++ nestedAssertions
    groups := groups ++ [values]
    bounds := bounds ++ requirements
  pure {
    mode := .ledgerCall
    inputs := inputs
    groups := groups
    returns := []
    assertions := conditions.flatMap (fun result => result.assertions ++ [result.term]) ++
      outputAssertions ++ guardConditions.flatMap (fun result => result.assertions ++ [result.term]) ++
      operationAssertions
    bounds := bounds ++ constraints ++ guards
  }

end Nightlean.Backend.Native
