import Nightlean.Semantics

namespace Nightlean.Helpers

/-- Declaration identity is independent of spelling and overload signatures. -/
structure DeclarationId where
  scope : Nat
  ordinal : Nat
  deriving Repr, BEq, DecidableEq, Inhabited

inductive ResultType where
  | unit
  | scalar (ty : Ty)
  deriving Repr, BEq, DecidableEq, Inhabited

inductive EffectKind where
  | witness | privateState | ledgerRead | ledgerWrite
  | assertion | fallibleCast | event | crossCall
  deriving Repr, BEq, DecidableEq

abbrev Effects := List EffectKind

def EffectKind.impure : EffectKind → Bool
  | .assertion | .fallibleCast => false
  | _ => true

structure Scope where
  id : Nat
  parent : Option Nat := none
  /-- A value binding stops function lookup through this scope. -/
  values : List String := []
  deriving Repr, Inhabited

structure Parameter where
  name : String
  ty : Ty
  deriving Repr, Inhabited

inductive Term where
  | unit
  | native (number : Nat)
  | bool (value : Bool)
  | uint (maximum number : Nat)
  | ref (name : String)
  | binary (op : ScalarPolicy.Binary) (left right : Term)
  | eq (left right : Term)
  | cast (target : Ty) (value : Term)
  | disclose (span : SourceSpan) (value : Term)
  | select (condition yes no : Term)
  | ite (condition yes no : Term)
  | andThen (left right : Term)
  | orElse (left right : Term)
  | witness (name : String) (ty : Ty)
  | poseidon2 (domain : Nat) (left right : Term)
  | call (name : String) (arguments : List Term)
  /-- An external-effect fixture has a typed result, but no native implementation.
  Its label is recorded by the reference trace evaluator. -/
  | effect (kind : EffectKind) (label : String) (result : Term)
  | at (span : SourceSpan) (value : Term)
  deriving Repr

inductive Statement where
  | bind (name : String) (ty : ResultType) (value : Term)
  | evaluate (value : Term)
  | assert (condition : Term)
  | «return» (value : Option Term := none)
  | branch (condition : Term) (yes no : List Statement)
  | stage (capability key : String) (ty : Ty) (value : Term)
  deriving Repr

structure Declaration where
  id : DeclarationId
  name : String
  parameters : List Parameter := []
  result : ResultType := .unit
  body : List Statement := []
  declaredPure : Bool := false
  span : SourceSpan := {}
  deriving Repr

structure Export where
  name : String
  target : DeclarationId
  inputs : List Input := []
  span : SourceSpan := {}
  deriving Repr

structure Program where
  scopes : List Scope := [{id := 0}]
  declarations : List Declaration := []
  exports : List Export := []
  deriving Repr

private def fail (span : SourceSpan) (message : String) : Except Diagnostic α :=
  .error {span, message}

private def liftError (span : SourceSpan) (value : Except String α) : Except Diagnostic α :=
  match value with
  | .ok result => .ok result
  | .error message => fail span message

/-- Local compiler resource policy, independent of Compact language limits.
Expanded nodes are a conservative preflight bound, not an emitted-node count. -/
structure Limits where
  maxDeclarations : Nat := 256
  maxScopes : Nat := 256
  maxExports : Nat := 256
  maxParameters : Nat := 64
  maxSourceNodes : Nat := 16384
  maxSourceDepth : Nat := 128
  maxCallDepth : Nat := 64
  maxAnalysisSteps : Nat := 65536
  maxExpandedNodes : Nat := 65536
  maxExpandedDepth : Nat := 256
  maxExecutionSteps : Nat := 131072
  deriving Repr, Inhabited

private def resource (span : SourceSpan) (kind : String) : Except Diagnostic α :=
  fail span s!"helper resource limit exceeded: {kind}"

private def validateLimits (limits : Limits) : Except Diagnostic Unit := do
  let hard : Limits := {}
  let fields := [
    ("declarations", limits.maxDeclarations, hard.maxDeclarations),
    ("scopes", limits.maxScopes, hard.maxScopes),
    ("exports", limits.maxExports, hard.maxExports),
    ("parameters", limits.maxParameters, hard.maxParameters),
    ("source nodes", limits.maxSourceNodes, hard.maxSourceNodes),
    ("source depth", limits.maxSourceDepth, hard.maxSourceDepth),
    ("call depth", limits.maxCallDepth, hard.maxCallDepth),
    ("call analysis steps", limits.maxAnalysisSteps, hard.maxAnalysisSteps),
    ("expanded nodes", limits.maxExpandedNodes, hard.maxExpandedNodes),
    ("expanded depth", limits.maxExpandedDepth, hard.maxExpandedDepth),
    ("execution steps", limits.maxExecutionSteps, hard.maxExecutionSteps)]
  for (name, actual, maximum) in fields do
    if actual > maximum then resource {} s!"requested {name} exceeds hard policy"

private def textMetadata (text : String) : Except Diagnostic Unit := do
  if text.utf8ByteSize > 1024 then resource {} "metadata text"

private def spanMetadata (span : SourceSpan) : Except Diagnostic Unit := do
  if span.file.utf8ByteSize > 1024 || span.line > 1000000000 || span.column > 1000000000 then
    resource {} "source-span metadata"

private def termMetadata : Term → Except Diagnostic Unit
  | .ref name | .call name _ | .witness name _ | .effect _ name _ => textMetadata name
  | .at span _ | .disclose span _ => spanMetadata span
  | _ => pure ()

private def statementMetadata : Statement → Except Diagnostic Unit
  | .bind name _ _ => textMetadata name
  | .stage capability key _ _ => do textMetadata capability; textMetadata key
  | _ => pure ()

private def statementTerms : Statement → List Term
  | .bind _ _ value | .evaluate value | .assert value | .stage _ _ _ value => [value]
  | .branch condition _ _ => [condition]
  | .return value => value.toList

/-- Traverse syntax with a bounded work list before invoking recursive passes. -/
private def scanTerms (limits : Limits) (span : SourceSpan) (available : Nat)
    (terms : List Term) : Except Diagnostic (Nat × Nat) := go available 0 0 (terms.map (·, 1))
where
  go : Nat → Nat → Nat → List (Term × Nat) → Except Diagnostic (Nat × Nat)
    | _, used, deepest, [] => pure (used, deepest)
    | 0, _, _, _ :: _ => resource span "source nodes"
    | fuel + 1, used, deepest, (term, depth) :: rest => do
      if depth > limits.maxSourceDepth then resource span "source depth"
      termMetadata term
      let children ← match term with
        | .binary _ a b | .eq a b | .poseidon2 _ a b
        | .andThen a b | .orElse a b => pure [a, b]
        | .cast _ value | .disclose _ value | .effect _ _ value | .at _ value => pure [value]
        | .select c a b | .ite c a b => pure [c, a, b]
        | .call _ arguments => do
          if arguments.length > limits.maxParameters then resource span "call arguments"
          pure arguments
        | _ => pure []
      go fuel (used + 1) (max deepest depth) (children.map (·, depth + 1) ++ rest)

private inductive SourceNode where
  | term (value : Term)
  | statement (value : Statement)

/-- Branch bodies share the source budget, including inactive and post-return syntax. -/
private def scanBody (limits : Limits) (span : SourceSpan) (available : Nat)
    (body : List Statement) : Except Diagnostic (Nat × Nat × Nat) :=
  if body.length > available then resource span "source nodes"
  else go available 0 0 0 (body.map fun value => (SourceNode.statement value, 0))
where
  go : Nat → Nat → Nat → Nat → List (SourceNode × Nat) → Except Diagnostic (Nat × Nat × Nat)
    | _, used, statements, deepest, [] => pure (used, statements, deepest)
    | 0, _, _, _, _ :: _ => resource span "source nodes"
    | fuel + 1, used, statements, deepest, (node, depth) :: rest => do
      if depth > limits.maxSourceDepth then resource span "source depth"
      let (children, statements) ← match node with
        | .statement value => do
          statementMetadata value
          let terms := (statementTerms value).map SourceNode.term
          let arms ← match value with
            | .branch _ yes no => do
              if yes.length + no.length > fuel then resource span "source nodes"
              pure ((yes ++ no).map SourceNode.statement)
            | _ => pure []
          pure (terms ++ arms, statements + 1)
        | .term value => do
          termMetadata value
          let terms ← match value with
            | .binary _ a b | .eq a b | .poseidon2 _ a b
            | .andThen a b | .orElse a b => pure [a, b]
            | .cast _ value | .disclose _ value | .effect _ _ value | .at _ value => pure [value]
            | .select c a b | .ite c a b => pure [c, a, b]
            | .call _ arguments => do
              if arguments.length > limits.maxParameters then resource span "call arguments"
              pure arguments
            | _ => pure []
          pure (terms.map SourceNode.term, statements)
      go fuel (used + 1) statements (max deepest depth)
        (children.map (·, depth + 1) ++ rest)

private structure SourceSize where
  nodes : Nat
  depth : Nat

private def sourcePreflight (limits : Limits) (program : Program) :
    Except Diagnostic (List (DeclarationId × SourceSize)) := do
  validateLimits limits
  if program.declarations.length > limits.maxDeclarations then resource {} "declarations"
  if program.scopes.length > limits.maxScopes then resource {} "scopes"
  if program.exports.length > limits.maxExports then resource {} "exports"
  for scope in program.scopes do
    if scope.id > 18446744073709551615 then resource {} "declaration identity metadata"
    if scope.values.length > limits.maxParameters then resource {} "scope bindings"
    for name in scope.values do textMetadata name
  for entry in program.exports do
    textMetadata entry.name
    spanMetadata entry.span
    if entry.target.scope > 18446744073709551615 || entry.target.ordinal > 18446744073709551615 then
      resource {} "declaration identity metadata"
    if entry.inputs.length > limits.maxParameters then resource entry.span "entry inputs"
    for input in entry.inputs do
      textMetadata input.name
      spanMetadata input.span
  let mut available := limits.maxSourceNodes
  let mut sizes := []
  for declaration in program.declarations do
    textMetadata declaration.name
    spanMetadata declaration.span
    if declaration.id.scope > 18446744073709551615 || declaration.id.ordinal > 18446744073709551615 then
      resource {} "declaration identity metadata"
    if declaration.parameters.length > limits.maxParameters then resource declaration.span "parameters"
    for parameter in declaration.parameters do textMetadata parameter.name
    let (nodes, statements, depth) ← scanBody limits declaration.span available declaration.body
    available := available - nodes
    sizes := (declaration.id, {
      nodes := 3 * (nodes + declaration.parameters.length + 2)
      depth := 3 * (statements + depth + declaration.parameters.length + 2)}) :: sizes
  pure sizes

def subtype : ResultType → ResultType → Bool
  | .unit, .unit => true
  | .scalar left, .scalar right =>
    left == right || match left, right with
      | .uint m, .uint n => m ≤ n
      | .uint _, .native => true
      | _, _ => false
  | _, _ => false

private def compatible (arguments : List ResultType) (parameters : List Parameter) : Bool :=
  arguments.length == parameters.length &&
    (arguments.zip parameters).all (fun (actual, parameter) => subtype actual (.scalar parameter.ty))

/-- Search one lexical group at a time. An ambiguous inner group never falls back. -/
private def resolveUnchecked (program : Program) (scope : Nat) (name : String) (arguments : List ResultType)
    (span : SourceSpan := {}) : Except Diagnostic Declaration := go (program.scopes.length + 1) scope
where
  go : Nat → Nat → Except Diagnostic Declaration
    | 0, _ => fail span "helper lexical scope cycle"
    | fuel + 1, scope => do
      let some group := program.scopes.find? (·.id == scope)
        | fail span "unknown helper lexical scope"
      if group.values.contains name then fail span s!"helper '{name}' is hidden by a value binding"
      let candidates := program.declarations.filter fun declaration =>
        declaration.id.scope == scope && declaration.name == name && compatible arguments declaration.parameters
      match candidates with
      | [declaration] => pure declaration
      | _ :: _ :: _ => fail span s!"ambiguous helper overload '{name}'"
      | [] => match group.parent with
        | some parent => go fuel parent
        | none => fail span s!"no compatible helper overload '{name}'"

def resolveWithLimits (limits : Limits) (program : Program) (scope : Nat) (name : String)
    (arguments : List ResultType) (span : SourceSpan := {}) : Except Diagnostic Declaration := do
  discard (sourcePreflight limits program)
  spanMetadata span
  textMetadata name
  if arguments.length > limits.maxParameters then resource span "call arguments"
  resolveUnchecked program scope name arguments span

def resolve (program : Program) (scope : Nat) (name : String) (arguments : List ResultType)
    (span : SourceSpan := {}) : Except Diagnostic Declaration :=
  resolveWithLimits {} program scope name arguments span

abbrev Environment := List (String × ResultType)

private def scalar (span : SourceSpan) : ResultType → Except Diagnostic Ty
  | .scalar ty => pure ty
  | .unit => fail span "unit is not a scalar helper argument"

private def common (span : SourceSpan) (left right : Ty) : Except Diagnostic Ty := do
  if subtype (.scalar left) (.scalar right) then pure right
  else if subtype (.scalar right) (.scalar left) then pure left
  else fail span "incompatible helper scalar types"

private def lookup (program : Program) (id : DeclarationId) (span : SourceSpan) : Except Diagnostic Declaration :=
  match program.declarations.find? (·.id == id) with
  | some declaration => pure declaration
  | none => fail span "unknown helper declaration identity"

structure TermInfo where
  ty : ResultType
  calls : List DeclarationId := []
  effects : Effects := []
  guarded : Bool := false
  deriving Repr, Inhabited

private def combine (ty : ResultType) (children : List TermInfo) (effects : Effects := []) : TermInfo :=
  {ty, calls := children.flatMap (·.calls), effects := (children.flatMap (·.effects) ++ effects).eraseDups, guarded := children.any (·.guarded)}

private def inferTerm (fuel : Nat) (program : Program) (scope : Nat) (env : Environment) (span : SourceSpan)
    (value : Term) : Except Diagnostic TermInfo :=
  match fuel with
  | 0 => resource span "type-analysis depth"
  | fuel + 1 => do
    match value with
    | .unit => pure {ty := .unit}
    | .native number =>
      unless number < Field.modulus do fail span "noncanonical helper native constant"
      pure {ty := .scalar .native}
    | .bool _ => pure {ty := .scalar .bool}
    | .uint maximum number =>
      liftError span (ScalarPolicy.validate (.uint maximum))
      unless number ≤ maximum do fail span "helper unsigned constant exceeds declared bound"
      pure {ty := .scalar (.uint maximum)}
    | .ref name =>
      let some ty := env.lookup name | fail span s!"unknown helper value '{name}'"
      pure {ty}
    | .binary op left right =>
      let left ← inferTerm fuel program scope env span left
      let right ← inferTerm fuel program scope env span right
      let lt ← scalar span left.ty
      let rt ← scalar span right.ty
      let result ← liftError span (ScalarPolicy.infer op lt.scalarKind rt.scalarKind)
      let ty := match result with
        | .native => Ty.native
        | .bool => .bool
        | .uint maximum => .uint maximum
      pure (combine (.scalar ty) [left, right]
        (if op == .sub && lt != .native && rt != .native then [.fallibleCast] else []))
    | .eq left right =>
      let left ← inferTerm fuel program scope env span left
      let right ← inferTerm fuel program scope env span right
      discard (common span (← scalar span left.ty) (← scalar span right.ty))
      pure (combine (.scalar .bool) [left, right])
    | .cast target value =>
      liftError span (target.validate {poseidon2 := true})
      let value ← inferTerm fuel program scope env span value
      discard (scalar span value.ty)
      pure (combine (.scalar target) [value] [.fallibleCast])
    | .disclose _ value => inferTerm fuel program scope env span value
    | .select condition yes no =>
      let condition ← inferTerm fuel program scope env span condition
      unless condition.ty == .scalar .bool do fail span "helper selector requires Bool"
      let yes ← inferTerm fuel program scope env span yes
      let no ← inferTerm fuel program scope env span no
      let ty ← common span (← scalar span yes.ty) (← scalar span no.ty)
      pure (combine (.scalar ty) [condition, yes, no])
    | .ite condition yes no =>
      let condition ← inferTerm fuel program scope env span condition
      unless condition.ty == .scalar .bool do fail span "helper condition requires Bool"
      let yes ← inferTerm fuel program scope env span yes
      let no ← inferTerm fuel program scope env span no
      let ty ← if subtype yes.ty no.ty then pure no.ty
        else if subtype no.ty yes.ty then pure yes.ty
        else fail span "conditional branches require one type to be a subtype of the other"
      pure {combine ty [condition, yes, no] with guarded := true}
    | .andThen left right | .orElse left right =>
      let left ← inferTerm fuel program scope env span left
      let right ← inferTerm fuel program scope env span right
      unless left.ty == .scalar .bool && right.ty == .scalar .bool do
        fail span "short-circuit operands require Bool"
      pure {combine (.scalar .bool) [left, right] with guarded := true}
    | .witness _ ty =>
      liftError span (ty.validate {poseidon2 := true})
      pure {ty := .scalar ty, effects := [.witness]}
    | .poseidon2 domain left right =>
      unless domain < Field.modulus do fail span "noncanonical helper hash domain"
      let left ← inferTerm fuel program scope env span left
      let right ← inferTerm fuel program scope env span right
      unless subtype left.ty (.scalar .native) && subtype right.ty (.scalar .native) do
        fail span "helper hash arguments require Native"
      pure (combine (.scalar .native) [left, right])
    | .call name arguments =>
      if (env.lookup name).isSome then fail span s!"helper '{name}' is hidden by a value binding"
      let arguments ← arguments.mapM (inferTerm fuel program scope env span)
      let declaration ← resolveUnchecked program scope name (arguments.map (·.ty)) span
      let info := combine declaration.result arguments
      pure {info with calls := declaration.id :: info.calls}
    | .effect kind _ result =>
      unless kind.impure do fail span "external helper effects require an external effect category"
      let result ← inferTerm fuel program scope env span result
      pure (combine result.ty [result] [kind])
    | .at span value => inferTerm fuel program scope env span value

def inferWithLimits (limits : Limits) (program : Program) (scope : Nat) (env : Environment)
    (span : SourceSpan) (value : Term) : Except Diagnostic TermInfo := do
  discard (sourcePreflight limits program)
  spanMetadata span
  discard (scanTerms limits span limits.maxSourceNodes [value])
  if env.length > limits.maxSourceNodes then resource span "type environment"
  for (name, _) in env do textMetadata name
  inferTerm limits.maxSourceDepth program scope env span value

def infer (program : Program) (scope : Nat) (env : Environment) (span : SourceSpan)
    (value : Term) : Except Diagnostic TermInfo :=
  inferWithLimits {} program scope env span value

structure Summary where
  id : DeclarationId
  calls : List DeclarationId
  direct : Effects
  effects : Effects := []
  guarded : Bool := false
  expandedNodes : Nat := 0
  expandedDepth : Nat := 0
  callDepth : Nat := 0
  deriving Repr, Inhabited

/-- Check all body syntax, including statements after a return. Execution still
stops at the first return. Branch syntax will use the same syntax-wide walk. -/
private structure BodyInfo where
  calls : List DeclarationId := []
  effects : Effects := []
  guarded : Bool := false
  returned : Bool := false
  deriving Inhabited

private def checkBody (limits : Limits) (program : Program) (declaration : Declaration)
    (fuel : Nat) (env : Environment) (body : List Statement) : Except Diagnostic BodyInfo :=
  match fuel with
  | 0 => resource declaration.span "statement-analysis depth"
  | fuel + 1 => do
    let span := declaration.span
    let mut env := env
    let mut result : BodyInfo := {}
    for statement in body do
      let info ← match statement with
        | .bind name ty value => do
          if let .scalar target := ty then liftError span (target.validate {poseidon2 := true})
          if (env.lookup name).isSome then fail span s!"duplicate helper value '{name}'"
          let info ← inferTerm limits.maxSourceDepth program declaration.id.scope env span value
          unless subtype info.ty ty do fail span "helper binding type mismatch"
          env := (name, ty) :: env
          pure info
        | .evaluate value => inferTerm limits.maxSourceDepth program declaration.id.scope env span value
        | .assert condition => do
          let info ← inferTerm limits.maxSourceDepth program declaration.id.scope env span condition
          unless info.ty == .scalar .bool do fail span "helper assertion requires Bool"
          pure {info with effects := (.assertion :: info.effects).eraseDups}
        | .return value => do
          let info ← match value with
            | some value => inferTerm limits.maxSourceDepth program declaration.id.scope env span value
            | none => pure {ty := .unit}
          unless subtype info.ty declaration.result do fail span "helper return type mismatch"
          result := {result with returned := true}
          pure info
        | .branch condition yes no => do
          let condition ← inferTerm limits.maxSourceDepth program declaration.id.scope env span condition
          unless condition.ty == .scalar .bool do fail span "helper condition requires Bool"
          let yes ← checkBody limits program declaration fuel env yes
          let no ← checkBody limits program declaration fuel env no
          result := {result with returned := result.returned || (yes.returned && no.returned)}
          pure {ty := .unit, calls := condition.calls ++ yes.calls ++ no.calls, effects := (condition.effects ++ yes.effects ++ no.effects).eraseDups, guarded := true}
        | .stage _ _ ty value => do
          liftError span (ty.validate {poseidon2 := true})
          let info ← inferTerm limits.maxSourceDepth program declaration.id.scope env span value
          unless subtype info.ty (.scalar ty) do fail span "private stage type mismatch"
          pure {info with effects := (.privateState :: info.effects).eraseDups}
      result := {result with
        calls := result.calls ++ info.calls
        effects := (result.effects ++ info.effects).eraseDups
        guarded := result.guarded || info.guarded}
    pure result

private def checkDeclarationUnchecked (limits : Limits) (program : Program) (declaration : Declaration) : Except Diagnostic Summary := do
  let span := declaration.span
  unless uniqueNames (declaration.parameters.map (·.name)) do fail span "duplicate helper parameter"
  let env := declaration.parameters.map fun parameter => (parameter.name, .scalar parameter.ty)
  for parameter in declaration.parameters do liftError span (parameter.ty.validate {poseidon2 := true})
  if let .scalar ty := declaration.result then liftError span (ty.validate {poseidon2 := true})
  let info ← checkBody limits program declaration limits.maxSourceDepth env declaration.body
  unless info.returned || declaration.result == .unit do fail span "helper fall-through returns unit, incompatible with declared result"
  pure {id := declaration.id, calls := info.calls, direct := info.effects, guarded := info.guarded}

def checkDeclarationWithLimits (limits : Limits) (program : Program) (declaration : Declaration) :
    Except Diagnostic Summary := do
  discard (sourcePreflight limits program)
  discard (sourcePreflight limits {program with declarations := [declaration]})
  checkDeclarationUnchecked limits program declaration

def checkDeclaration (program : Program) (declaration : Declaration) : Except Diagnostic Summary :=
  checkDeclarationWithLimits {} program declaration

private structure AnalysisState where
  remaining : Nat
  cache : List Summary := []
  deriving Inhabited

private def saturatedAdd (limit left right : Nat) : Nat := min (limit + 1) (left + right)

/-- Cache summaries before another call site traverses the same callee. Keep
call-site multiplicity when adding expansion bounds, including duplicate edges. -/
private def summarize (limits : Limits) (summaries : List Summary)
    (sizes : List (DeclarationId × SourceSize)) (span : SourceSpan) (id : DeclarationId) :
    StateT AnalysisState (Except Diagnostic) Summary := go limits.maxCallDepth [] id
where
  go : Nat → List DeclarationId → DeclarationId → StateT AnalysisState (Except Diagnostic) Summary
    | fuel, stack, id => do
      let state ← get
      if state.remaining == 0 then liftM (resource span "call analysis steps")
      set {state with remaining := state.remaining - 1}
      if stack.contains id then liftM (fail span "reachable recursive helper call cycle")
      if let some cached := state.cache.find? (·.id == id) then
        if cached.callDepth > fuel then liftM (resource span "call depth")
        return cached
      match fuel with
      | 0 => liftM (resource span "call depth")
      | fuel + 1 =>
        let some summary := summaries.find? (·.id == id)
          | liftM (fail span "unknown helper call graph identity")
        let children ← summary.calls.mapM (go fuel (id :: stack))
        let direct := sizes.lookup id |>.getD {nodes := 0, depth := 0}
        let expandedNodes := children.foldl
          (fun count child => saturatedAdd limits.maxExpandedNodes count child.expandedNodes)
          direct.nodes
        if expandedNodes > limits.maxExpandedNodes then liftM (resource span "expanded nodes")
        let expandedDepth := saturatedAdd limits.maxExpandedDepth direct.depth
          ((children.map (·.expandedDepth)).foldl max 0)
        if expandedDepth > limits.maxExpandedDepth then liftM (resource span "expanded depth")
        let result := {summary with
          effects := (summary.direct ++ children.flatMap (·.effects)).eraseDups
          guarded := summary.guarded || children.any (·.guarded)
          expandedNodes
          expandedDepth
          callDepth := 1 + (children.map (·.callDepth)).foldl max 0}
        modify fun state => {state with cache := result :: state.cache}
        pure result

/-- Unreachable recursion is pruned before cycle/purity analysis. Every declared
signature and statement is still statically checked. -/
def analyzeWithLimits (limits : Limits) (program : Program) : Except Diagnostic (List Summary) := do
  let sizes ← sourcePreflight limits program
  unless uniqueNames (program.scopes.map (toString ∘ Scope.id)) do fail {} "duplicate helper scope identity"
  unless (program.declarations.map (·.id)).eraseDups.length == program.declarations.length do
    fail {} "duplicate helper declaration identity"
  unless uniqueNames (program.exports.map (·.name)) do fail {} "duplicate monomorphic helper entrypoint name"
  for scope in program.scopes do
    let mut next := scope.parent
    let mut seen := [scope.id]
    for _ in List.range (program.scopes.length + 1) do
      if let some id := next then
        if seen.contains id then fail {} "helper lexical scope cycle"
        let some parent := program.scopes.find? (·.id == id) | fail {} "unknown parent helper scope"
        seen := id :: seen
        next := parent.parent
  for declaration in program.declarations do
    unless program.scopes.any (·.id == declaration.id.scope) do fail declaration.span "unknown declaration scope"
  let summaries ← program.declarations.mapM (checkDeclarationUnchecked limits program)
  let mut state : AnalysisState := {remaining := limits.maxAnalysisSteps}
  for entry in program.exports do
    let declaration ← lookup program entry.target entry.span
    unless uniqueNames (entry.inputs.map (·.name)) do fail entry.span "duplicate helper entrypoint input"
    for input in entry.inputs do liftError input.span (input.ty.validate {poseidon2 := true})
    unless compatible (entry.inputs.map fun input => .scalar input.ty) declaration.parameters do
      fail entry.span "helper entrypoint input signature mismatch"
    let (_, next) ← (summarize limits summaries sizes entry.span entry.target).run state
    state := next
  let mut results := []
  for summary in summaries do
    if let some result := state.cache.find? (·.id == summary.id) then
      let declaration ← lookup program summary.id {}
      if declaration.declaredPure && result.effects.any EffectKind.impure then
        fail declaration.span s!"declared-pure helper '{declaration.name}' has transitive effects"
      results := results ++ [result]
  pure results

def analyze (program : Program) : Except Diagnostic (List Summary) :=
  analyzeWithLimits {} program

/-- Resource-checked query closures avoid rescanning a whole program for each
node in another checked pass. Each standalone query retains local input caps. -/
structure Prepared where
  program : Program
  summaries : List Summary
  infer : Nat → Environment → SourceSpan → Term → Except Diagnostic TermInfo
  resolve : Nat → String → List ResultType → SourceSpan → Except Diagnostic Declaration

def prepareWithLimits (limits : Limits) (program : Program) : Except Diagnostic Prepared := do
  let summaries ← analyzeWithLimits limits program
  pure {
    program, summaries
    infer := fun scope env span value => do
      spanMetadata span
      discard (scanTerms limits span limits.maxSourceNodes [value])
      if env.length > limits.maxSourceNodes then resource span "type environment"
      for (name, _) in env do textMetadata name
      inferTerm limits.maxSourceDepth program scope env span value
    resolve := fun scope name arguments span => do
      spanMetadata span
      textMetadata name
      if arguments.length > limits.maxParameters then resource span "call arguments"
      resolveUnchecked program scope name arguments span
  }

structure Scalar where
  ty : Ty
  value : Expr ty
  deriving Repr

instance : Inhabited Scalar := ⟨⟨.bool, .bool true⟩⟩

/-- Unit uses an unobservable internal Bool token, so scalar sequencing still
retains unused arguments, assertions and fallible casts. -/
structure Lowered where
  ty : ResultType
  scalar : Scalar
  deriving Inhabited

private def unitValue : Lowered := ⟨.unit, ⟨.bool, .bool true⟩⟩

private def coerce (span : SourceSpan) (value : Lowered) (target : ResultType) : Except Diagnostic Lowered := do
  unless subtype value.ty target do fail span "helper lowering type mismatch"
  match target with
  | .unit => pure value
  | .scalar ty =>
    if h : value.scalar.ty = ty then pure ⟨target, ⟨ty, h ▸ value.scalar.value⟩⟩
    else pure ⟨target, ⟨ty, .cast ty value.scalar.value⟩⟩

private def boolExpr (span : SourceSpan) (value : Lowered) : Except Diagnostic (Expr .bool) :=
  if h : value.scalar.ty = .bool then pure (h ▸ value.scalar.value)
  else fail span "helper lowering expected Bool"

private def nativeExpr (span : SourceSpan) (value : Lowered) : Except Diagnostic (Expr .native) := do
  let value ← coerce span value (.scalar .native)
  if h : value.scalar.ty = .native then pure (h ▸ value.scalar.value)
  else fail span "helper lowering expected Native"

private def typedExpr (span : SourceSpan) (target : Ty) (value : Lowered) : Except Diagnostic (Expr target) := do
  let value ← coerce span value (.scalar target)
  if h : value.scalar.ty = target then pure (h ▸ value.scalar.value)
  else fail span "helper lowering expected declared scalar type"

private def sequence (name : String) (value body : Lowered) : Lowered :=
  {body with scalar := ⟨body.scalar.ty, .letE name value.scalar.value body.scalar.value⟩}

private abbrev LowerEnv := List (String × Lowered)
private structure LowerState where
  next : Nat := 0
  reserved : List String := []
  remaining : Nat
  deriving Inhabited

private abbrev LowerM := StateT LowerState (Except Diagnostic)

private def spendLower (span : SourceSpan) : LowerM Unit := do
  let state ← get
  if state.remaining == 0 then liftM (resource span "lowering steps")
  set {state with remaining := state.remaining - 1}

private def fresh : LowerM String := do
  let state ← get
  let start := state.next
  let reserved := state.reserved
  let some n := (List.range (reserved.length + 1)).map (· + start) |>.find?
    (fun n => !reserved.contains s!"$helper{n}")
    | liftM (fail {} "helper fresh binding exhaustion")
  set {state with next := n + 1}
  pure s!"$helper{n}"

private def liftD (value : Except Diagnostic α) : LowerM α := liftM value

mutual
  private partial def lowerTerm (program : Program) (scope : Nat) (env : LowerEnv)
      (span : SourceSpan) (term : Term) : LowerM Lowered := do
    spendLower span
    match term with
    | .unit => pure unitValue
    | .native n => pure ⟨.scalar .native, ⟨.native, .native n⟩⟩
    | .bool b => pure ⟨.scalar .bool, ⟨.bool, .bool b⟩⟩
    | .uint m n => pure ⟨.scalar (.uint m), ⟨.uint m, .uint m n⟩⟩
    | .ref name =>
      let some value := env.lookup name | liftD (fail span s!"unbound helper value '{name}'")
      pure value
    | .binary op left right =>
      let left ← lowerTerm program scope env span left
      let right ← lowerTerm program scope env span right
      match left.scalar, right.scalar with
      | ⟨.uint m, a⟩, ⟨.uint n, b⟩ =>
        match op with
        | .add => pure ⟨.scalar (.uint (m+n)), ⟨.uint (m+n), .uadd a b⟩⟩
        | .sub => pure ⟨.scalar (.uint m), ⟨.uint m, .usub a b⟩⟩
        | .mul => pure ⟨.scalar (.uint (m*n)), ⟨.uint (m*n), .umul a b⟩⟩
      | _, _ =>
        let left ← liftD (nativeExpr span left)
        let right ← liftD (nativeExpr span right)
        let value := match op with | .add => Expr.add left right | .sub => .sub left right | .mul => .mul left right
        pure ⟨.scalar .native, ⟨.native, value⟩⟩
    | .eq left right =>
      let left ← lowerTerm program scope env span left
      let right ← lowerTerm program scope env span right
      let ty ← liftD (common span left.scalar.ty right.scalar.ty)
      let left ← liftD (typedExpr span ty left)
      let right ← liftD (typedExpr span ty right)
      let value := Expr.eq left right
      pure ⟨.scalar .bool, ⟨.bool, value⟩⟩
    | .cast target value =>
      let value ← lowerTerm program scope env span value
      pure ⟨.scalar target, ⟨target, .cast target value.scalar.value⟩⟩
    | .disclose release value =>
      let value ← lowerTerm program scope env span value
      pure {value with scalar := ⟨value.scalar.ty, .disclose release value.scalar.value⟩}
    | .select condition yes no =>
      let condition ← lowerTerm program scope env span condition
      let yes ← lowerTerm program scope env span yes
      let no ← lowerTerm program scope env span no
      let ty ← liftD (common span yes.scalar.ty no.scalar.ty)
      pure ⟨.scalar ty, ⟨ty, .select (← liftD (boolExpr span condition))
        (← liftD (typedExpr span ty yes)) (← liftD (typedExpr span ty no))⟩⟩
    | .ite .. | .andThen .. | .orElse .. =>
      liftD (fail span "native helper capability unavailable: structured control (CF-02)")
    | .witness .. => liftD (fail span "native helper capability unavailable: witness")
    | .poseidon2 domain left right =>
      let left ← lowerTerm program scope env span left
      let right ← lowerTerm program scope env span right
      pure ⟨.scalar .native, ⟨.native, .poseidon2 domain
        (← liftD (nativeExpr span left)) (← liftD (nativeExpr span right))⟩⟩
    | .call name arguments =>
      let values ← arguments.mapM (lowerTerm program scope env span)
      let declaration ← liftD (resolveUnchecked program scope name (values.map (·.ty)) span)
      lowerCall program declaration values span
    | .effect kind label _ => liftD (fail span s!"native helper capability unavailable: {repr kind} ({label})")
    | .at span value => lowerTerm program scope env span value

  private partial def lowerCall (program : Program) (declaration : Declaration)
      (values : List Lowered) (span : SourceSpan) : LowerM Lowered := do
    spendLower span
    let mut env := []
    let mut bindings := []
    for (parameter, actual) in declaration.parameters.zip values do
      spendLower span
      let actual ← liftD (coerce span actual (.scalar parameter.ty))
      let name ← fresh
      bindings := bindings ++ [(name, actual)]
      env := (parameter.name, ⟨.scalar parameter.ty, ⟨parameter.ty, .ref name⟩⟩) :: env
    let body ← lowerBody program declaration env declaration.body
    pure (bindings.foldr (fun (name, value) body => sequence name value body) body)

  private partial def lowerBody (program : Program) (declaration : Declaration)
      (env : LowerEnv) (body : List Statement) : LowerM Lowered := do
    spendLower declaration.span
    match body with
    | [] => pure unitValue
    | .return value :: _ =>
      let value ← match value with
        | none => pure unitValue
        | some value => lowerTerm program declaration.id.scope env declaration.span value
      liftD (coerce declaration.span value declaration.result)
    | statement :: rest =>
      match statement with
      | .bind name ty value =>
        let value ← lowerTerm program declaration.id.scope env declaration.span value
        let value ← liftD (coerce declaration.span value ty)
        let localName ← fresh
        let reference : Lowered := ⟨ty, ⟨value.scalar.ty, .ref localName⟩⟩
        let body ← lowerBody program declaration ((name, reference) :: env) rest
        pure (sequence localName value body)
      | .evaluate value =>
        let value ← lowerTerm program declaration.id.scope env declaration.span value
        let name ← fresh
        let body ← lowerBody program declaration env rest
        pure (sequence name value body)
      | .assert condition =>
        let condition ← lowerTerm program declaration.id.scope env declaration.span condition
        let body ← lowerBody program declaration env rest
        pure {body with scalar := ⟨body.scalar.ty, .assertE (← liftD (boolExpr declaration.span condition)) body.scalar.value⟩}
      | .branch .. => liftD (fail declaration.span "native helper capability unavailable: structured control (CF-02)")
      | .stage .. => liftD (fail declaration.span "native helper capability unavailable: private state")
      | .return _ => liftD (fail declaration.span "invalid helper statement sequence")
end

/-- Compilation always performs typing, call-graph/purity analysis and DF-00.
No caller-supplied summary or disclosure exemption is accepted. -/
def compileWithLimits (limits : Limits) (program : Program) (entryName : String) : Except Diagnostic Circuit := do
  let summaries ← analyzeWithLimits limits program
  for summary in summaries do
    if summary.guarded then fail {} "native helper capability unavailable: structured control (CF-02)"
    if let some effect := summary.effects.find? EffectKind.impure then
      let declaration ← lookup program summary.id {}
      fail declaration.span s!"native helper capability unavailable: {repr effect}"
  let some entry := program.exports.find? (·.name == entryName) | fail {} "unknown helper entrypoint"
  let declaration ← lookup program entry.target entry.span
  let values := entry.inputs.map fun input =>
    (⟨.scalar input.ty, ⟨input.ty, .ref input.name⟩⟩ : Lowered)
  let (body, _) ← (lowerCall program declaration values entry.span).run {reserved := entry.inputs.map (·.name), remaining := limits.maxExecutionSteps}
  let outputName := ((List.range (entry.inputs.length + 1)).map fun n =>
    if n == 0 then "result" else s!"result{n}").find?
      (fun name => !(entry.inputs.map (·.name)).contains name) |>.getD "result"
  let outputs := match declaration.result with
    | .unit => []
    | .scalar _ => [{name := outputName, ty := body.scalar.ty, value := body.scalar.value, span := entry.span}]
  let circuit : Circuit := {
    name := entry.name, inputs := entry.inputs, outputs, span := entry.span
    constraints := if declaration.result == .unit then [.letE "$unit" body.scalar.value (.bool true)] else []
  }
  circuit.validate {poseidon2 := true}
  Disclosure.circuit circuit
  pure circuit

def compile (program : Program) (entryName : String) : Except Diagnostic Circuit :=
  compileWithLimits {} program entryName

private abbrev TraceValue := Option ScalarPolicy.Value
private abbrev TraceEnv := List (String × TraceValue)
private structure TraceState where
  events : List String := []
  remaining : Nat
  deriving Inhabited

private abbrev TraceM := StateT TraceState (Except Diagnostic)

private def spendTrace (span : SourceSpan) : TraceM Unit := do
  let state ← get
  if state.remaining == 0 then liftM (resource span "evaluation steps")
  set {state with remaining := state.remaining - 1}

private def traceScalar (span : SourceSpan) (value : TraceValue) : TraceM ScalarPolicy.Value :=
  match value with
  | some value => pure value
  | none => liftM (fail span "unit used as scalar in helper trace")

private def traceType : TraceValue → ResultType
  | none => .unit
  | some value => .scalar (match value.kind with
    | .native => .native | .bool => .bool | .uint m => .uint m)

private def traceCast (span : SourceSpan) (value : TraceValue) (ty : ResultType) : TraceM TraceValue := do
  match ty with
  | .unit => pure none
  | .scalar ty =>
    let value ← traceScalar span value
    some <$> liftM (liftError span (ScalarPolicy.cast value ty.scalarKind))

mutual
  private partial def traceTerm (program : Program) (ctx : EvalContext) (scope : Nat)
      (env : TraceEnv) (span : SourceSpan) (term : Term) : TraceM TraceValue := do
    spendTrace span
    match term with
    | .unit => pure none
    | .native n => pure (some ⟨.native, n⟩)
    | .bool b => pure (some ⟨.bool, if b then 1 else 0⟩)
    | .uint m n => pure (some ⟨.uint m, n⟩)
    | .ref name =>
      let some value := env.lookup name | liftM (fail span "unbound helper trace value")
      pure value
    | .binary op left right =>
      let left ← traceTerm program ctx scope env span left >>= traceScalar span
      let right ← traceTerm program ctx scope env span right >>= traceScalar span
      some <$> liftM (liftError span (ScalarPolicy.evaluate op left right))
    | .cast target value =>
      let value ← traceTerm program ctx scope env span value
      traceCast span value (.scalar target)
    | .eq left right =>
      let left ← traceTerm program ctx scope env span left
      let right ← traceTerm program ctx scope env span right
      let ty ← liftM (common span (← liftM (scalar span (traceType left)))
        (← liftM (scalar span (traceType right))))
      let left ← traceCast span left (.scalar ty)
      let right ← traceCast span right (.scalar ty)
      pure (some ⟨.bool, if left == right then 1 else 0⟩)
    | .select condition yes no =>
      let condition ← traceTerm program ctx scope env span condition >>= traceScalar span
      let yes ← traceTerm program ctx scope env span yes
      let no ← traceTerm program ctx scope env span no
      let ty ← liftM (common span (← liftM (scalar span (traceType yes)))
        (← liftM (scalar span (traceType no))))
      traceCast span (if condition.number == 0 then no else yes) (.scalar ty)
    | .ite condition yes no =>
      let condition ← traceTerm program ctx scope env span condition >>= traceScalar span
      let result ← traceTerm program ctx scope env span (if condition.number == 0 then no else yes)
      let info ← liftM (inferTerm 128 program scope (env.map fun (name, value) => (name, traceType value)) span term)
      traceCast span result info.ty
    | .andThen left right =>
      let left ← traceTerm program ctx scope env span left >>= traceScalar span
      if left.number == 0 then pure (some left) else traceTerm program ctx scope env span right
    | .orElse left right =>
      let left ← traceTerm program ctx scope env span left >>= traceScalar span
      if left.number != 0 then pure (some left) else traceTerm program ctx scope env span right
    | .witness .. => liftM (fail span "registered witness execution requires the portable control runtime")
    | .disclose _ value => traceTerm program ctx scope env span value
    | .poseidon2 domain left right =>
      let left ← traceTerm program ctx scope env span left >>= traceScalar span
      let right ← traceTerm program ctx scope env span right >>= traceScalar span
      let result ← liftM (liftError span (ctx.poseidon2 domain left.number right.number))
      let value : ScalarPolicy.Value := ⟨.native, result⟩
      liftM (liftError span value.validate)
      pure (some value)
    | .call name arguments =>
      let values ← arguments.mapM (traceTerm program ctx scope env span)
      let declaration ← liftM (resolveUnchecked program scope name (values.map traceType) span)
      traceCall program ctx declaration values
    | .effect _ label result =>
      let result ← traceTerm program ctx scope env span result
      modify fun state => {state with events := label :: state.events}
      pure result
    | .at span value => traceTerm program ctx scope env span value

  private partial def traceCall (program : Program) (ctx : EvalContext) (declaration : Declaration)
      (values : List TraceValue) : TraceM TraceValue := do
    spendTrace declaration.span
    let env ← (declaration.parameters.zip values).mapM fun (parameter, value) => do
      spendTrace declaration.span
      pure (parameter.name, ← traceCast declaration.span value (.scalar parameter.ty))
    traceBody program ctx declaration env declaration.body

  private partial def traceBody (program : Program) (ctx : EvalContext) (declaration : Declaration)
      (env : TraceEnv) (body : List Statement) : TraceM TraceValue := do
    pure (← traceBlock program ctx declaration env body).2

  private partial def traceBlock (program : Program) (ctx : EvalContext) (declaration : Declaration)
      (env : TraceEnv) (body : List Statement) : TraceM (Bool × TraceValue) := do
    spendTrace declaration.span
    match body with
    | [] => pure (false, none)
    | .return none :: _ => pure (true, none)
    | .return (some value) :: _ =>
      let value ← traceTerm program ctx declaration.id.scope env declaration.span value
      pure (true, ← traceCast declaration.span value declaration.result)
    | .bind name ty value :: rest =>
      let value ← traceTerm program ctx declaration.id.scope env declaration.span value
      let value ← traceCast declaration.span value ty
      traceBlock program ctx declaration ((name, value) :: env) rest
    | .evaluate value :: rest =>
      discard (traceTerm program ctx declaration.id.scope env declaration.span value)
      traceBlock program ctx declaration env rest
    | .assert condition :: rest =>
      let condition ← traceTerm program ctx declaration.id.scope env declaration.span condition >>= traceScalar declaration.span
      unless condition.number == 1 do liftM (fail declaration.span "helper assertion failed")
      traceBlock program ctx declaration env rest
    | .branch condition yes no :: rest =>
      let condition ← traceTerm program ctx declaration.id.scope env declaration.span condition >>= traceScalar declaration.span
      let result ← traceBlock program ctx declaration env (if condition.number == 0 then no else yes)
      if result.1 then pure result else traceBlock program ctx declaration env rest
    | .stage _ _ _ _ :: _ => liftM (fail declaration.span "private staging requires the portable control runtime")
end

/-- Deterministic effect fixtures validate source evaluation order separately
from native capability support. No witness callback or external side effect runs. -/
def traceWithLimits (limits : Limits) (program : Program) (ctx : EvalContext) (entryName : String)
    (inputs : List ScalarPolicy.Value) : Except Diagnostic (TraceValue × List String) := do
  discard (analyzeWithLimits limits program)
  let some entry := program.exports.find? (·.name == entryName) | fail {} "unknown helper trace entrypoint"
  let declaration ← lookup program entry.target entry.span
  unless inputs.length == entry.inputs.length do fail entry.span "helper trace input count mismatch"
  for (input, value) in entry.inputs.zip inputs do
    liftError input.span value.validate
    unless traceType (some value) == .scalar input.ty do fail input.span "helper trace input type mismatch"
  let (result, state) ← (traceCall program ctx declaration (inputs.map some)).run
    {remaining := limits.maxExecutionSteps}
  pure (result, state.events.reverse)

def trace (program : Program) (ctx : EvalContext) (entryName : String)
    (inputs : List ScalarPolicy.Value) : Except Diagnostic (TraceValue × List String) :=
  traceWithLimits {} program ctx entryName inputs

/-- Discarding a parameter cannot discard a failing actual argument. -/
theorem argument_failure_preserved (ctx : EvalContext) (env : EvalEnv)
    (name : String) (argument : Expr source) (body : Expr result) (message : String)
    (h : argument.eval ctx env = .error message) :
    (Expr.letE name argument body).eval ctx env = .error message := by
  rw [Expr.eval, h]
  rfl

/-- The binding introduced for a helper parameter transfers actual origins
without releasing them, even when parameter and caller spellings coincide. -/
theorem parameter_origins_preserved (env : Disclosure.Environment) (name : String)
    (argument : Expr source) :
    Disclosure.origins env (Expr.letE name argument (Expr.ref name : Expr source)) =
      Disclosure.origins env argument := by
  simp only [Disclosure.origins]
  cases Disclosure.origins env argument <;> simp [List.lookup]

end Nightlean.Helpers
