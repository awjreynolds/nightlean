import Noctium.Helpers

namespace Noctium.Helpers.Iteration

open Noctium
open Noctium.Helpers

structure ParameterSpec where
  name : String
  type : Option ResultType := none
  deriving Repr

inductive Operator where
  | named (name : String)
  | anonymous (parameters : List ParameterSpec) (result : Option ResultType := none)
      (body : List Statement)
  deriving Repr

private def failAt {α : Type} (span : SourceSpan) (message : String) : Except Diagnostic α :=
  .error {span, message}

private def appendUnique (names more : List String) : List String :=
  more.foldl (fun result name => if result.contains name then result else result ++ [name]) names

private def appendMany (groups : List (List String)) : List String :=
  groups.foldl appendUnique []

private partial def termReferences (term : Term) : List String :=
  match term with
  | .ref name => [name]
  | .binary _ left right | .boolAnd left right | .boolOr left right | .boolXor left right
  | .eq left right | .poseidon2 _ left right | .andThen left right | .orElse left right =>
    appendUnique (termReferences left) (termReferences right)
  | .cast _ value | .disclose _ value | .effect _ _ value | .at _ value
  | .project value _ | .bytesAt value _ => termReferences value
  | .select condition yes no | .ite condition yes no =>
    appendMany [termReferences condition, termReferences yes, termReferences no]
  | .witnessCall _ _ arguments | .call _ arguments | .composite _ arguments
  | .curve _ arguments | .bytes _ arguments => appendMany (arguments.map termReferences)
  | .index value index => appendUnique (termReferences value) (termReferences index)
  | _ => []

private partial def bodyFreeReferences (bound : List String) : List Statement → List String
  | [] => []
  | .bind name _ value :: rest =>
    appendUnique (termReferences value |>.filter fun ref => !bound.contains ref)
      (bodyFreeReferences (name :: bound) rest)
  | .evaluate value :: rest | .assert value :: rest =>
    appendUnique (termReferences value |>.filter fun ref => !bound.contains ref)
      (bodyFreeReferences bound rest)
  | .return value :: rest =>
    appendUnique (appendMany (value.toList.map termReferences) |>.filter fun ref => !bound.contains ref)
      (bodyFreeReferences bound rest)
  | .branch condition yes no :: rest =>
    appendMany [termReferences condition |>.filter fun ref => !bound.contains ref,
      bodyFreeReferences bound yes, bodyFreeReferences bound no, bodyFreeReferences bound rest]
  | .forRange index _ _ body :: rest =>
    appendUnique (bodyFreeReferences (index :: bound) body) (bodyFreeReferences bound rest)
  | .stage _ _ _ value :: rest | .writeCell _ _ value :: rest =>
    appendUnique (termReferences value |>.filter fun ref => !bound.contains ref)
      (bodyFreeReferences bound rest)
  | .readCell _ destination _ :: rest => bodyFreeReferences (destination :: bound) rest
  | .readMap _ destination _ _ key :: rest | .readMember _ destination _ _ key :: rest =>
    appendUnique (termReferences key |>.filter fun ref => !bound.contains ref)
      (bodyFreeReferences (destination :: bound) rest)
  | .writeMap _ _ _ key value :: rest =>
    appendUnique (termReferences key |>.filter fun ref => !bound.contains ref)
      (appendUnique (termReferences value |>.filter fun ref => !bound.contains ref)
        (bodyFreeReferences bound rest))

private def projectionNames : Types.Projection → List String
  | .field name => [name]
  | .enumField variant field => [variant, field]
  | _ => []

private partial def compositeNames : Types.CompositeType → List String
  | .structure id | .enumeration id => [id]
  | .tuple items => appendMany (items.map compositeNames)
  | .vector _ element => compositeNames element
  | _ => []

private partial def termNames (term : Term) : List String :=
  match term with
  | .ref name | .witness name _ => [name]
  | .effect _ name result => appendUnique [name] (termNames result)
  | .call name arguments => appendUnique [name] (appendMany (arguments.map termNames))
  | .witnessCall site name arguments => appendMany [[site, name], appendMany (arguments.map termNames)]
  | .composite type leaves => appendMany [compositeNames type, appendMany (leaves.map termNames)]
  | .project value projection => appendUnique (termNames value) (projectionNames projection)
  | .binary _ left right | .boolAnd left right | .boolOr left right | .boolXor left right
  | .eq left right | .poseidon2 _ left right | .andThen left right | .orElse left right
  | .index left right => appendUnique (termNames left) (termNames right)
  | .cast _ value | .disclose _ value | .at _ value | .bytesAt value _ => termNames value
  | .select condition yes no | .ite condition yes no =>
    appendMany [termNames condition, termNames yes, termNames no]
  | .curve _ arguments | .bytes _ arguments => appendMany (arguments.map termNames)
  | _ => []

private partial def statementNames : List Statement → List String
  | [] => []
  | .bind name _ value :: rest => appendMany [[name], termNames value, statementNames rest]
  | .evaluate value :: rest | .assert value :: rest => appendUnique (termNames value) (statementNames rest)
  | .return value :: rest => appendUnique (appendMany (value.toList.map termNames)) (statementNames rest)
  | .branch condition yes no :: rest =>
    appendMany [termNames condition, statementNames yes, statementNames no, statementNames rest]
  | .forRange index _ _ body :: rest => appendMany [[index], statementNames body, statementNames rest]
  | .stage capability key _ value :: rest =>
    appendMany [[capability, key], termNames value, statementNames rest]
  | .readCell state destination _ :: rest => appendMany [[state, destination], statementNames rest]
  | .writeCell state _ value :: rest => appendMany [[state], termNames value, statementNames rest]
  | .readMap state destination _ _ key :: rest | .readMember state destination _ _ key :: rest =>
    appendMany [[state, destination], termNames key, statementNames rest]
  | .writeMap state _ _ key value :: rest =>
    appendMany [[state], termNames key, termNames value, statementNames rest]

private partial def termCallsHiddenBy (hidden : List String) (span : SourceSpan) :
    Term → Except Diagnostic Unit
  | .call name arguments => do
    if hidden.contains name then failAt span s!"helper '{name}' is hidden by a value binding"
    arguments.forM (termCallsHiddenBy hidden span)
  | .witnessCall _ _ arguments | .composite _ arguments | .curve _ arguments | .bytes _ arguments =>
    arguments.forM (termCallsHiddenBy hidden span)
  | .binary _ left right | .boolAnd left right | .boolOr left right | .boolXor left right
  | .eq left right | .poseidon2 _ left right | .andThen left right | .orElse left right
  | .index left right => do
    termCallsHiddenBy hidden span left
    termCallsHiddenBy hidden span right
  | .cast _ value | .disclose _ value | .effect _ _ value | .at _ value
  | .project value _ | .bytesAt value _ => termCallsHiddenBy hidden span value
  | .select condition yes no | .ite condition yes no => do
    termCallsHiddenBy hidden span condition
    termCallsHiddenBy hidden span yes
    termCallsHiddenBy hidden span no
  | _ => pure ()

private partial def bodyCallsHiddenBy (span : SourceSpan) (outer : List String)
    (bound : List String) : List Statement → Except Diagnostic Unit
  | [] => pure ()
  | .bind name _ value :: rest => do
    termCallsHiddenBy (bound ++ outer.filter fun hidden => !bound.contains hidden) span value
    bodyCallsHiddenBy span outer (name :: bound) rest
  | .evaluate value :: rest | .assert value :: rest => do
    termCallsHiddenBy (bound ++ outer.filter fun hidden => !bound.contains hidden) span value
    bodyCallsHiddenBy span outer bound rest
  | .return value :: rest => do
    value.forM (termCallsHiddenBy (bound ++ outer.filter fun hidden => !bound.contains hidden) span)
    bodyCallsHiddenBy span outer bound rest
  | .branch condition yes no :: rest => do
    termCallsHiddenBy (bound ++ outer.filter fun hidden => !bound.contains hidden) span condition
    bodyCallsHiddenBy span outer bound yes
    bodyCallsHiddenBy span outer bound no
    bodyCallsHiddenBy span outer bound rest
  | .forRange index _ _ body :: rest => do
    bodyCallsHiddenBy span outer (index :: bound) body
    bodyCallsHiddenBy span outer bound rest
  | .stage _ _ _ value :: rest | .writeCell _ _ value :: rest => do
    termCallsHiddenBy (bound ++ outer.filter fun hidden => !bound.contains hidden) span value
    bodyCallsHiddenBy span outer bound rest
  | .readCell _ destination _ :: rest => bodyCallsHiddenBy span outer (destination :: bound) rest
  | .readMap _ destination _ _ key :: rest | .readMember _ destination _ _ key :: rest => do
    termCallsHiddenBy (bound ++ outer.filter fun hidden => !bound.contains hidden) span key
    bodyCallsHiddenBy span outer (destination :: bound) rest
  | .writeMap _ _ _ key value :: rest => do
    let hidden := bound ++ outer.filter fun name => !bound.contains name
    termCallsHiddenBy hidden span key
    termCallsHiddenBy hidden span value
    bodyCallsHiddenBy span outer bound rest

private def resultTypeOfComposite : Types.CompositeType → ResultType
  | .unit => .unit
  | .scalar ty => .scalar ty
  | type => .composite type

private def resultTypeNames : ResultType → List String
  | .composite type => compositeNames type
  | _ => []

private def programNames (program : Program) (env : Environment) : List String :=
  appendMany [env.map Prod.fst,
    program.scopes.flatMap (·.values),
    program.declarations.flatMap fun declaration =>
      declaration.name :: declaration.parameters.map (·.name) ++
        declaration.compositeParameters.map Prod.fst ++ statementNames declaration.body,
    program.exports.flatMap fun entry =>
      entry.name :: entry.inputs.map (·.name) ++ entry.compositeInputs.map (·.name),
    program.witnesses.flatMap fun signature =>
      [signature.name, signature.operation, signature.capability] ++
        signature.parameters.map (·.name) ++ signature.privateKey.toList,
    program.ledger.map (·.name),
    program.composites.structures.map (·.id),
    program.composites.enumerations.map (·.id)]

private def freshText (used : List String) (stem : String) : String :=
  ((List.range (used.length + 1)).map fun index =>
    if index == 0 then stem else stem ++ "_" ++ toString index).find?
      (fun candidate => !used.contains candidate) |>.getD (stem ++ "_fresh")

private def generatedIdentity (limits : Limits) (program : Program) (scope : Nat)
    (used : List String) : Except Diagnostic (String × DeclarationId) := do
  unless program.scopes.any (·.id == scope) do failAt {} "unknown iteration helper scope"
  if program.declarations.length >= limits.maxDeclarations then
    failAt {} "helper resource limit exceeded: declarations"
  let some ordinal := (List.range (program.declarations.length + 1)).find?
      (fun ordinal => !program.declarations.any (fun declaration =>
        declaration.id == ⟨scope, ordinal⟩))
    | failAt {} "helper declaration identity exhaustion"
  let name := freshText used s!"_noctium_iteration_{scope}_{ordinal}"
  pure (name, ⟨scope, ordinal⟩)

private def inferType (limits : Limits) (program : Program) (scope : Nat) (env : Environment)
    (span : SourceSpan) (term : Term) : Except Diagnostic ResultType := do
  return (← Noctium.Helpers.inferWithLimits limits program scope env span term).ty

private def declarationParameters (parameters : List (String × ResultType)) :
    List Parameter × List (String × Types.CompositeType) := Id.run do
  let mut scalars := []
  let mut composites := []
  for (name, type) in parameters do
    match type with
    | .scalar ty => scalars := scalars ++ [({name := name, ty := ty} : Parameter)]
    | .composite composite =>
      scalars := scalars ++ [({name := name, ty := .native} : Parameter)]
      composites := composites ++ [(name, composite)]
    | .unit =>
      scalars := scalars ++ [({name := name, ty := .native} : Parameter)]
      composites := composites ++ [(name, .unit)]
  return (scalars, composites)

private def addCheckedDeclaration (limits : Limits) (program : Program)
    (declaration : Declaration) : Except Diagnostic Program := do
  let candidate := {program with declarations := program.declarations ++ [declaration]}
  discard (Noctium.Helpers.syntacticPreflight limits candidate)
  discard (Noctium.Helpers.checkDeclarationWithLimits limits candidate declaration)
  pure candidate

private partial def bodyHasReturn : List Statement → Bool
  | [] => false
  | .return _ :: _ => true
  | .branch _ yes no :: rest => bodyHasReturn yes || bodyHasReturn no || bodyHasReturn rest
  | .forRange _ _ _ body :: rest => bodyHasReturn body || bodyHasReturn rest
  | _ :: rest => bodyHasReturn rest

private def commonReturnType (span : SourceSpan) (types : List ResultType) :
    Except Diagnostic ResultType := do
  match types with
  | [] => pure .unit
  | first :: rest => rest.foldlM (fun common next =>
      if subtype common next then pure next
      else if subtype next common then pure common
      else failAt span "anonymous operator return types have no common type") first

/-- Infer only missing return signatures. The full generated body still passes
through Helpers.checkDeclarationWithLimits before it is exposed. -/
private partial def inferBodyReturns (limits : Limits) (program : Program) (scope : Nat)
    (span : SourceSpan) (initial : Environment) (body : List Statement) :
    Except Diagnostic (List ResultType) := do
  let mut env := initial
  let mut returns := []
  for statement in body do
    match statement with
    | .bind name type value => do
      let actual ← inferType limits program scope env span value
      unless subtype actual type do failAt span "helper binding type mismatch"
      env := (name, type) :: env
    | .return none => returns := returns ++ [.unit]
    | .return (some value) => returns := returns ++ [← inferType limits program scope env span value]
    | .branch _ yes no => do
      returns := returns ++ (← inferBodyReturns limits program scope span env yes)
      returns := returns ++ (← inferBodyReturns limits program scope span env no)
    | .forRange index _ _ body => do
      if bodyHasReturn body then failAt span "return cannot escape a finite range body"
      let _ ← inferBodyReturns limits program scope span ((index, .scalar .native) :: env) body
    | .readCell _ destination type => env := (destination, .scalar type) :: env
    | .readMap _ destination _ valueType _ => env := (destination, .scalar valueType) :: env
    | .readMember _ destination _ valueType _ => env := (destination, .scalar valueType) :: env
    | _ => pure ()
  pure returns

private structure MaterializedOperator where
  program : Program
  name : String
  captures : List (String × ResultType)
  parameters : List ResultType
  result : ResultType

private def environmentType (env : Environment) (name : String) : Option ResultType :=
  (env.find? (·.1 == name)).map Prod.snd

private def preflightAnonymousBody (limits : Limits) (program : Program) (scope : Nat)
    (env : Environment) (span : SourceSpan) (specifications : List ParameterSpec)
    (actualTypes : List ResultType) (body : List Statement) : Except Diagnostic Unit := do
  let used := programNames program env
  let (name, id) ← generatedIdentity limits program scope used
  let parameters := (specifications.zip actualTypes).map fun (specification, type) =>
    (specification.name, type)
  let (scalarParameters, compositeParameters) := declarationParameters parameters
  let probe : Declaration := {
    id, name, parameters := scalarParameters, compositeParameters,
    result := .unit, body, span}
  discard (Noctium.Helpers.syntacticPreflight limits
    {program with declarations := program.declarations ++ [probe]})

private def materializeOperator (limits : Limits) (program : Program) (scope : Nat)
    (env : Environment) (span : SourceSpan) (operator : Operator)
    (actualTypes : List ResultType) : Except Diagnostic MaterializedOperator := do
  discard (Noctium.Helpers.syntacticPreflight limits program)
  discard (inferType limits program scope env span .unit)
  match operator with
  | .named name => do
    if (environmentType env name).isSome then
      failAt span s!"helper '{name}' is hidden by a value binding"
    let declaration ← Noctium.Helpers.resolveWithLimits limits program scope name actualTypes span
    let parameters := declaration.parameters.map fun parameter => declaration.parameterType parameter
    pure {program, name, captures := [], parameters, result := declaration.result}
  | .anonymous specifications resultAnnotation body => do
    if specifications.length != actualTypes.length then
      failAt span "anonymous operator argument count mismatch"
    if specifications.length > limits.maxParameters then
      failAt span "helper resource limit exceeded: operator parameters"
    preflightAnonymousBody limits program scope env span specifications actualTypes body
    unless (specifications.map (·.name)).eraseDups.length == specifications.length do
      failAt span "duplicate anonymous operator parameter"
    let mut parameters := []
    for (specification, actual) in specifications.zip actualTypes do
      let type := specification.type.getD actual
      unless subtype actual type do failAt span "anonymous operator parameter type mismatch"
      parameters := parameters ++ [(specification.name, type)]
    let freeNames := bodyFreeReferences (specifications.map (·.name)) body
    let mut captures : List (String × ResultType) := []
    for name in freeNames do
      if let some type := environmentType env name then
        captures := captures ++ [(name, type)]
    let parameterEnv := (captures ++ parameters)
    let returnType ← match resultAnnotation with
      | some result => pure result
      | none => do
        let returns ← inferBodyReturns limits program scope span parameterEnv body
        commonReturnType span returns
    discard (bodyCallsHiddenBy span (env.map Prod.fst) (specifications.map (·.name)) body)
    let namedParameters := captures ++ parameters
    if namedParameters.length > limits.maxParameters then
      failAt span "helper resource limit exceeded: parameters"
    let used := appendMany [programNames program env, statementNames body,
      specifications.map (·.name), namedParameters.map Prod.fst,
      namedParameters.flatMap fun (_, type) => resultTypeNames type,
      resultTypeNames returnType]
    let (name, id) ← generatedIdentity limits program scope used
    let (declParams, compositeParams) := declarationParameters namedParameters
    let declaration : Declaration := {
      id, name, parameters := declParams, compositeParameters := compositeParams,
      result := returnType, body, span}
    let program ← addCheckedDeclaration limits program declaration
    pure {program, name, captures, parameters := parameters.map Prod.snd, result := returnType}

private def actualArgumentTypes (limits : Limits) (program : Program) (scope : Nat)
    (env : Environment) (span : SourceSpan) (arguments : List Term) :
    Except Diagnostic (List ResultType) := do
  if arguments.length > limits.maxParameters then
    failAt span "helper resource limit exceeded: call arguments"
  arguments.mapM (inferType limits program scope env span)

def applyWithLimits (limits : Limits) (program : Program) (scope : Nat)
    (env : Environment) (span : SourceSpan) (operator : Operator) (arguments : List Term) :
    Except Diagnostic (Program × Term) := do
  let argumentTypes ← actualArgumentTypes limits program scope env span arguments
  let compiled ← materializeOperator limits program scope env span operator argumentTypes
  let callArguments := compiled.captures.map fun capture => Term.ref capture.1
  let term := Term.call compiled.name (callArguments ++ arguments)
  discard (inferType limits compiled.program scope env span term)
  pure (compiled.program, term)

private def checkedComposite (program : Program) (span : SourceSpan)
    (type : Types.CompositeType) : Except Diagnostic Types.CompiledType :=
  match Types.compileType program.composites type with
  | .ok compiled => pure compiled
  | .error diagnostic => failAt (if diagnostic.span.file.isEmpty then span else diagnostic.span)
      diagnostic.message

private def mapElementType : ResultType → Types.CompositeType
  | .unit => .unit
  | .scalar (.bytes length) => .bytes length
  | .scalar ty => .scalar ty
  | .composite type => type

private partial def layoutHasEnum : Types.Layout → Bool
  | .enumeration .. => true
  | .tuple items => items.any layoutHasEnum
  | .structure _ fields => fields.any fun (_, field) => layoutHasEnum field
  | .vector _ element => layoutHasEnum element
  | .unit | .scalar _ | .bytes _ _ => false

private partial def layoutProjectionDepth : Types.Layout → Nat
  | .unit | .scalar _ | .enumeration .. => 0
  | .tuple items =>
    if items.all (fun item => item.leafCount == 0) then 0
    else 1 + (items.map layoutProjectionDepth).foldl max 0
  | .structure _ fields =>
    if fields.all (fun (_, field) => field.leafCount == 0) then 0
    else 1 + (fields.map (layoutProjectionDepth ∘ Prod.snd)).foldl max 0
  | .vector length element =>
    if length == 0 || element.leafCount == 0 then 0 else 1 + layoutProjectionDepth element
  | .bytes length _ => if length == 0 then 0 else 1

private partial def flattenLayoutTerms (span : SourceSpan) : Types.Layout → Term →
    Except Diagnostic (List Term)
  | .unit, _ => pure []
  | .scalar _, value => pure [value]
  | .tuple items, value => do
    let parts ← (List.range items.length).mapM fun index => do
      let some item := items[index]? | failAt span "checked tuple layout index mismatch"
      if item.leafCount == 0 then pure []
      else flattenLayoutTerms span item (.project value (.tupleIndex index))
    pure parts.flatten
  | .structure _ fields, value => do
    let parts ← fields.mapM fun (name, field) => do
      if field.leafCount == 0 then pure []
      else flattenLayoutTerms span field (.project value (.field name))
    pure parts.flatten
  | .vector length element, value => do
    let parts ← if element.leafCount == 0 then pure [] else
      (List.range length).mapM fun index =>
        flattenLayoutTerms span element (.project value (.vectorIndex index))
    pure parts.flatten
  | .bytes length _, value =>
    (List.range length).mapM fun index => pure (.project value (.byteIndex index))
  | .enumeration .., _ => failAt span "map results containing enum layouts are unsupported"

private def flattenMapResult (span : SourceSpan) (result : ResultType)
    (layout : Types.Layout) (value : Term) : Except Diagnostic (List Term) := do
  match result, layout with
  | .scalar (.bytes length), .bytes layoutLength _ => do
    unless length == layoutLength do failAt span "checked byte result layout mismatch"
    (List.range length).mapM fun index => pure (.bytesAt value index)
  | _, layout => flattenLayoutTerms span layout value

private def vectorElement (limits : Limits) (program : Program) (scope : Nat)
    (env : Environment) (span : SourceSpan) (sequence : Term) :
    Except Diagnostic (Nat × Types.CompositeType) := do
  let inferred ← inferType limits program scope env span sequence
  let .composite (.vector length element) := inferred
    | failAt span "iteration sequence must be a fixed vector expression"
  if length > Types.defaultLimits.maxVectorLength then
    failAt span "helper resource limit exceeded: iteration vector length"
  discard (checkedComposite program span (.vector length element))
  pure (length, element)

private def freshNames (used : List String) (stems : List String) : List String := Id.run do
  let mut reserved := used
  let mut names := []
  for stem in stems do
    let name := freshText reserved stem
    names := names ++ [name]
    reserved := reserved ++ [name]
  return names

private def makeWrapper (limits : Limits) (program : Program) (scope : Nat)
    (span : SourceSpan) (used : List String) (parameters : List (String × ResultType))
    (result : ResultType) (body : List Statement) : Except Diagnostic (Program × String) := do
  if parameters.length > limits.maxParameters then
    failAt span "helper resource limit exceeded: wrapper parameters"
  let (name, id) ← generatedIdentity limits program scope used
  let (scalarParameters, compositeParameters) := declarationParameters parameters
  let declaration : Declaration := {
    id, name, parameters := scalarParameters, compositeParameters, result, body, span}
  let program ← addCheckedDeclaration limits program declaration
  pure (program, name)

private def checkedWrapperCall (limits : Limits) (program : Program) (scope : Nat)
    (env : Environment) (span : SourceSpan) (name : String) (arguments : List Term) :
    Except Diagnostic (Program × Term) := do
  if arguments.length > limits.maxParameters then
    failAt span "helper resource limit exceeded: wrapper call arguments"
  let term := Term.call name arguments
  discard (inferType limits program scope env span term)
  pure (program, term)

private def operatorNames : Operator → List String
  | .named name => [name]
  | .anonymous parameters result body => appendMany [
      parameters.map (·.name), statementNames body, result.toList.flatMap resultTypeNames]

private def checkGeneratedSourceBudget (limits : Limits) (span : SourceSpan)
    (nodes : Nat) : Except Diagnostic Unit := do
  if nodes > limits.maxSourceNodes then failAt span "helper resource limit exceeded: source nodes"

/-- Apply an operator once to each element of one or more fixed vector
expressions. Sequence expressions become wrapper arguments, so each evaluates
once before the wrapper body starts. -/
def mapWithLimits (limits : Limits) (program : Program) (scope : Nat)
    (env : Environment) (span : SourceSpan) (sequences : List Term) (operator : Operator) :
    Except Diagnostic (Program × Term) := do
  discard (Noctium.Helpers.syntacticPreflight limits program)
  discard (inferType limits program scope env span .unit)
  if sequences.isEmpty then failAt span "map requires at least one sequence"
  if sequences.length > limits.maxParameters then
    failAt span "helper resource limit exceeded: map sequences"
  let typedSequences ← sequences.mapM fun sequence => do
    let (length, element) ← vectorElement limits program scope env span sequence
    pure (length, element)
  let some (length, _) := typedSequences.head?
    | failAt span "map requires at least one sequence"
  unless typedSequences.all (fun item => item.1 == length) do
    failAt span "map sequence lengths must match"
  let actualTypes := typedSequences.map fun (_, element) => resultTypeOfComposite element
  let compiled ← materializeOperator limits program scope env span operator actualTypes
  if let .composite (.scalar _) := compiled.result then
    failAt span "map cannot flatten a composite scalar wrapper"
  let outputElementType := mapElementType compiled.result
  let compiledResultType ← checkedComposite compiled.program span outputElementType
  if layoutHasEnum compiledResultType.checked.value then
    failAt span "map results containing enum layouts are unsupported"
  let vectorType := Types.CompositeType.vector length outputElementType
  discard (checkedComposite compiled.program span vectorType)
  if compiled.captures.length + actualTypes.length > limits.maxParameters then
    failAt span "helper resource limit exceeded: map operator arguments"
  if sequences.length + compiled.captures.length > limits.maxParameters then
    failAt span "helper resource limit exceeded: map wrapper arguments"
  let resultLeaves := compiledResultType.checked.expandedLeaves
  unless resultLeaves ≤ compiledResultType.checked.expandedNodes do
    failAt span "checked map result leaf count exceeds its expansion bound"
  let projectionDepth := layoutProjectionDepth compiledResultType.checked.value
  unless projectionDepth ≤ compiledResultType.checked.layoutNodes do
    failAt span "checked map result projection depth exceeds its layout bound"
  let projectedTerms := length * resultLeaves * (projectionDepth + 1)
  let projectionWork := length *
    (compiledResultType.checked.expandedNodes - resultLeaves)
  let estimatedNodes := length * (2 + compiled.captures.length + 2 * sequences.length) +
    projectedTerms + projectionWork + 2
  checkGeneratedSourceBudget limits span estimatedNodes
  let used := appendMany [programNames compiled.program env, sequences.flatMap termNames,
    operatorNames operator, compiled.captures.map Prod.fst]
  let sequenceNames := freshNames used (List.range sequences.length |>.map fun i =>
    s!"_noctium_map_sequence_{i}")
  let reserved := used ++ sequenceNames
  let resultNames := freshNames reserved (List.range length |>.map fun i =>
    s!"_noctium_map_result_{i}")
  let wrapperParameters := (sequenceNames.zip typedSequences).map fun (name, typed) =>
    (name, .composite (.vector typed.1 typed.2))
  let wrapperParameters := wrapperParameters ++ compiled.captures
  let operationCalls := (List.range length).map fun index =>
    let elements := sequenceNames.zip typedSequences |>.map fun (name, _) =>
      Term.project (.ref name) (.vectorIndex index)
    Term.call compiled.name (compiled.captures.map (fun capture => Term.ref capture.1) ++ elements)
  let bindings := resultNames.zip operationCalls |>.map fun (name, value) =>
    Statement.bind name compiled.result value
  let leaves ← (List.range length).mapM fun index =>
    flattenMapResult span compiled.result compiledResultType.checked.value (.ref resultNames[index]!)
  let leaves := leaves.flatten
  let wrapperBody := bindings ++ [
    .return (some (.composite vectorType leaves))]
  let (compiledProgram, wrapperName) ← makeWrapper limits compiled.program scope span
    (appendMany [used, sequenceNames, resultNames]) wrapperParameters
    (.composite vectorType) wrapperBody
  checkedWrapperCall limits compiledProgram scope env span wrapperName
    (sequences ++ compiled.captures.map fun capture => Term.ref capture.1)

/-- Fold a fixed vector using an operator whose accumulator parameter and result
share one exact type. The initial expression runs before the sequence. -/
def foldWithLimits (limits : Limits) (program : Program) (scope : Nat)
    (env : Environment) (span : SourceSpan) (initial sequence : Term) (operator : Operator) :
    Except Diagnostic (Program × Term) := do
  discard (Noctium.Helpers.syntacticPreflight limits program)
  discard (inferType limits program scope env span .unit)
  let initialType ← inferType limits program scope env span initial
  let (length, element) ← vectorElement limits program scope env span sequence
  let elementType := resultTypeOfComposite element
  let compiled ← materializeOperator limits program scope env span operator [initialType, elementType]
  let [accumulatorType, operatorElementType] := compiled.parameters
    | failAt span "fold operator must accept accumulator and element parameters"
  unless subtype initialType accumulatorType do
    failAt span "fold initial value is incompatible with its accumulator parameter"
  unless compiled.result == accumulatorType do
    failAt span "fold operator result must exactly match its accumulator parameter"
  unless subtype elementType operatorElementType do
    failAt span "fold element type is incompatible with its operator parameter"
  if compiled.captures.length + 2 > limits.maxParameters then
    failAt span "helper resource limit exceeded: fold operator arguments"
  let estimatedNodes := 4 + length * (5 + compiled.captures.length)
  checkGeneratedSourceBudget limits span estimatedNodes
  let used := appendMany [programNames compiled.program env, termNames initial,
    termNames sequence, operatorNames operator, compiled.captures.map Prod.fst]
  let freshParams := freshNames used ["_noctium_fold_initial", "_noctium_fold_sequence"]
  let [initialName, sequenceName] := freshParams
    | failAt span "fold wrapper name allocation failed"
  let accumulatorNames := freshNames (used ++ [initialName, sequenceName])
    (List.range (length + 1) |>.map fun index => s!"_noctium_fold_acc_{index}")
  let wrapperParameters := [
    (initialName, initialType),
    (sequenceName, .composite (.vector length element))] ++ compiled.captures
  let mut body := [Statement.bind accumulatorNames.head! accumulatorType (.ref initialName)]
  for index in List.range length do
    let accumulator := accumulatorNames[index]!
    let nextAccumulator := accumulatorNames[index + 1]!
    let elementTerm := Term.project (.ref sequenceName) (.vectorIndex index)
    let call := Term.call compiled.name
      (compiled.captures.map (fun capture => Term.ref capture.1) ++
        [Term.ref accumulator, elementTerm])
    body := body ++ [Statement.bind nextAccumulator accumulatorType call]
  body := body ++ [.return (some (.ref accumulatorNames[length]!))]
  let (compiledProgram, wrapperName) ← makeWrapper limits compiled.program scope span
    (appendMany [used, [initialName, sequenceName], accumulatorNames]) wrapperParameters
    accumulatorType body
  checkedWrapperCall limits compiledProgram scope env span wrapperName
    (initial :: sequence :: compiled.captures.map fun capture => Term.ref capture.1)

end Noctium.Helpers.Iteration
