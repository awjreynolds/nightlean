import Nightlean.Disclosure
import Nightlean.Helpers
import Nightlean.Helpers.Specialization
import Nightlean.ComponentDisclosure
import Nightlean.Control
import Nightlean.Witness
import Nightlean.Modules
import Nightlean.Backend.Impact
import Lean

namespace Nightlean
open Lean Elab Command

/-- Declarations registered through the supported Nightlean circuit surface. -/
structure CircuitInfo where
  declName : Name
  inputs : List (String × Ty)
  publicInputs : List (String × Ty)
  outputs : List (String × Ty)
  sourceProgram? : Option (Name × String) := none
  specializationArtifact? : Option String := none
  deriving Inhabited

initialize circuitRegistry : SimplePersistentEnvExtension CircuitInfo (Array CircuitInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }
initialize contractRegistry : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

initialize controlRegistry : SimplePersistentEnvExtension Name (Array Name) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

structure WitnessInfo where
  circuitName : Name
  sourceName : Name
  exportName : String
  deriving Inhabited

/-- Exact source constants registered as Noctium module definitions. -/
structure ModuleSourceInfo where
  sourceName : Name
  definitionName : Name
  deriving Inhabited

/-- A module contract declaration retains only source roots. Compiler checks
re-expand these roots and rebuild their concrete circuits for each invocation. -/
structure ModuleBuildInfo where
  contractName : Name
  requestName : Name
  deriving Inhabited

structure ModuleCircuitBuildInfo where
  source : Modules.ModuleCircuitSource
  declarationName : Name
  programName : Name
  program : Helpers.Program
  circuit : Circuit
  signatureArtifact : Helpers.Specialization.SignatureArtifact

structure ModuleBuildOutput where
  specialized : Modules.SpecializedModule
  contract : Contract
  programs : List (Name × Name × Helpers.Program)
  circuits : List ModuleCircuitBuildInfo

initialize witnessRegistry : SimplePersistentEnvExtension WitnessInfo (Array WitnessInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

initialize moduleSourceRegistry : SimplePersistentEnvExtension ModuleSourceInfo (Array ModuleSourceInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

initialize moduleBuildRegistry : SimplePersistentEnvExtension ModuleBuildInfo (Array ModuleBuildInfo) ←
  registerSimplePersistentEnvExtension {
    addImportedFn := fun entries => entries.foldl (init := #[]) (· ++ ·)
    addEntryFn := Array.push
  }

declare_syntax_cat nltype
scoped syntax "Native" : nltype
scoped syntax "Bool" : nltype
scoped syntax "UInt" num : nltype
scoped syntax "UIntRange" num : nltype
scoped syntax "Bytes32" : nltype

declare_syntax_cat nlexpr
scoped syntax ident : nlexpr
scoped syntax num : nlexpr
scoped syntax "true" : nlexpr
scoped syntax "false" : nlexpr
scoped syntax "let" ident ":=" nlexpr "in" nlexpr : nlexpr
scoped syntax "assertThen(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "add(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "mul(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "sub(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "uint(" num ")" : nlexpr
scoped syntax "cast(" nltype "," nlexpr ")" : nlexpr
scoped syntax "default(" nltype ")" : nlexpr
scoped syntax "disclose(" nlexpr ")" : nlexpr
scoped syntax "eq(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "select(" nlexpr "," nlexpr "," nlexpr ")" : nlexpr
scoped syntax "poseidon2(" num "," nlexpr "," nlexpr ")" : nlexpr

declare_syntax_cat nlcstmt
scoped syntax "public" ident ":" nltype : nlcstmt
scoped syntax "private" ident ":" nltype : nlcstmt
scoped syntax "let" ident ":" nltype ":=" nlexpr : nlcstmt
scoped syntax "assert" nlexpr : nlcstmt
scoped syntax "output" ident ":" nltype ":=" nlexpr : nlcstmt
scoped syntax (name := circuitCommand) "nightlean_circuit" ident "where" nlcstmt* "end" : command

declare_syntax_cat nlstate
scoped syntax "cell" ident ":" nltype : nlstate
scoped syntax "map" ident ":" nltype "=>" nltype : nlstate

declare_syntax_cat nleffect
scoped syntax "read" ident "as" ident : nleffect
scoped syntax "read" ident "[" nlexpr "]" "as" ident : nleffect
scoped syntax "member" ident "[" nlexpr "]" "as" ident : nleffect
scoped syntax "require" nlexpr : nleffect
scoped syntax "absent" ident "[" nlexpr "]" : nleffect
scoped syntax "write" ident ":=" nlexpr : nleffect
scoped syntax "insert" ident "[" nlexpr "]" ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "write" ident ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "insert" ident "[" nlexpr "]" ":=" nlexpr : nleffect
scoped syntax "when" nlexpr "require" nlexpr : nleffect
scoped syntax "when" nlexpr "read" ident "as" ident : nleffect
scoped syntax "when" nlexpr "read" ident "[" nlexpr "]" "as" ident : nleffect
scoped syntax "when" nlexpr "member" ident "[" nlexpr "]" "as" ident : nleffect

declare_syntax_cat nlstatement
scoped syntax nleffect : nlstatement
scoped syntax "if" nlexpr "then" "{" nlstatement* "}" "else" "{" nlstatement* "}" : nlstatement

declare_syntax_cat nlentry
scoped syntax "entry" ident "uses" ident "where" nlstatement* "end" : nlentry
scoped syntax (name := contractCommand) "nightlean_contract" ident "where" nlstate* nlentry* "end" : command

open scoped Nightlean

private def readTy (stx : TSyntax `nltype) : CommandElabM Ty :=
  match stx with
  | `(nltype| Native) => pure .native
  | `(nltype| Bool) => pure .bool
  | `(nltype| UInt $bits:num) =>
    match ScalarPolicy.sized bits.getNat with
    | .ok (.uint maximum) => pure (.uint maximum)
    | .error message => throwErrorAt stx message
    | _ => throwErrorAt stx "invalid unsigned width"
  | `(nltype| UIntRange $exclusive:num) =>
    match ScalarPolicy.bounded exclusive.getNat with
    | .ok (.uint maximum) => pure (.uint maximum)
    | .error message => throwErrorAt stx message
    | _ => throwErrorAt stx "invalid unsigned range"
  | `(nltype| Bytes32) => pure (.bytes 32)
  | _ => throwErrorAt stx "unsupported Nightlean type"

private def tyTerm : Ty → CommandElabM (TSyntax `term)
  | .native => `(Nightlean.Ty.native)
  | .bool => `(Nightlean.Ty.bool)
  | .uint maximum => `(Nightlean.Ty.uint $(⟨Syntax.mkNumLit (toString maximum)⟩))
  | .bytes length => `(Nightlean.Ty.bytes $(⟨Syntax.mkNumLit (toString length)⟩))

private def stringTerm (value : String) : TSyntax `term := ⟨Syntax.mkStrLit value⟩
private def natTerm (value : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString value)⟩

private def spanTerm (stx : Syntax) : CommandElabM (TSyntax `term) := do
  let fileMap ← getFileMap
  let pos := fileMap.toPosition (stx.getPos?.getD 0)
  let file ← getFileName
  `({ file := $(stringTerm file), line := $(natTerm pos.line),
      column := $(natTerm (pos.column + 1)) : Nightlean.SourceSpan })

private abbrev Bindings := List (String × Ty × TSyntax `term)

private def coerceExpression (stx : Syntax) (found target : Ty) (value : TSyntax `term) :
    CommandElabM (TSyntax `term) := do
  if found == target then return value
  match found, target with
  | .uint m, .uint n =>
    unless m ≤ n do throwErrorAt stx "Nightlean expression type mismatch; use an explicit narrowing cast"
    `(Nightlean.Expr.cast $(← tyTerm target) $value)
  | .uint _, .native => `(Nightlean.Expr.cast Nightlean.Ty.native $value)
  | _, _ => throwErrorAt stx "Nightlean expression type mismatch"

private def commonType (stx : Syntax) (left right : Ty) : CommandElabM Ty := do
  if left == right then return left
  match left, right with
  | .uint m, .uint n => pure (.uint (max m n))
  | .native, .uint _ | .uint _, .native => pure .native
  | _, _ => throwErrorAt stx "Nightlean expression type mismatch"

/-- A new partial scalar operation must execute even beneath a total wrapper.
Mark every subtraction conservatively, including total native-field subtraction. -/
private partial def hasPartialScalar (stx : TSyntax `nlexpr) : _root_.Bool :=
  match stx with
  | `(nlexpr| cast($_:nltype, $_:nlexpr)) => Bool.true
  | `(nlexpr| sub($_:nlexpr, $_:nlexpr)) => Bool.true
  | `(nlexpr| assertThen($_:nlexpr, $_:nlexpr)) => Bool.true
  | `(nlexpr| let $_:ident := $value:nlexpr in $body:nlexpr) =>
    hasPartialScalar value || hasPartialScalar body
  | `(nlexpr| disclose($value)) => hasPartialScalar value
  | `(nlexpr| add($a, $b)) | `(nlexpr| mul($a, $b))
  | `(nlexpr| eq($a, $b)) | `(nlexpr| poseidon2($_:num, $a, $b)) =>
    hasPartialScalar a || hasPartialScalar b
  | `(nlexpr| select($c, $a, $b)) =>
    hasPartialScalar c || hasPartialScalar a || hasPartialScalar b
  | _ => Bool.false

private partial def expression (env : Bindings) (stx : TSyntax `nlexpr) :
    CommandElabM (Ty × TSyntax `term) := do
  match stx with
  | `(nlexpr| $id:ident) =>
    match env.find? (fun p => p.1 == id.getId.toString) with
    | some (_, ty, value) => pure (ty, value)
    | none => throwErrorAt id "unknown Nightlean value '{id.getId}'"
  | `(nlexpr| $n:num) => pure (.native, ← `(Nightlean.Expr.native $n))
  | `(nlexpr| true) => pure (.bool, ← `(Nightlean.Expr.bool Bool.true))
  | `(nlexpr| false) => pure (.bool, ← `(Nightlean.Expr.bool Bool.false))
  | `(nlexpr| let $id:ident := $value:nlexpr in $body:nlexpr) => do
    let (valueTy, value) ← expression env value
    let typeTerm ← tyTerm valueTy
    let valueRef ← `(Nightlean.Expr.ref (ty := $typeTerm) $(stringTerm id.getId.toString))
    let bodyEnv := (id.getId.toString, valueTy, valueRef) :: env
    let (bodyTy, body) ← expression bodyEnv body
    pure (bodyTy, ← `(Nightlean.Expr.letE $(stringTerm id.getId.toString) $value $body))
  | `(nlexpr| assertThen($condition, $body)) => do
    let condition ← expected env condition .bool
    let (bodyTy, body) ← expression env body
    pure (bodyTy, ← `(Nightlean.Expr.assertE $condition $body))
  | `(nlexpr| uint($n:num)) =>
    match ScalarPolicy.validate (.uint n.getNat) with
    | .error message => throwErrorAt stx message
    | .ok _ => pure (.uint n.getNat, ← `(Nightlean.Expr.uint $n $n))
  | `(nlexpr| cast($target:nltype, $value:nlexpr)) =>
    let target ← readTy target
    let (_, value) ← expression env value
    pure (target, ← `(Nightlean.Expr.cast $(← tyTerm target) $value))
  | `(nlexpr| default($target:nltype)) =>
    let target ← readTy target
    match target with
    | .native => pure (.native, ← `(Nightlean.Expr.native 0))
    | .bool => pure (.bool, ← `(Nightlean.Expr.bool Bool.false))
    | .uint maximum => pure (target, ← `(Nightlean.Expr.uint $(natTerm maximum) 0))
    | .bytes _ => throwErrorAt stx "Bytes32 has no scalar default expression"
  | `(nlexpr| disclose($value)) =>
    let (ty, value) ← expression env value
    pure (ty, ← `(Nightlean.Expr.disclose $(← spanTerm stx) $value))
  | `(nlexpr| add($a, $b)) =>
    arithmetic env stx .add a b
  | `(nlexpr| mul($a, $b)) =>
    arithmetic env stx .mul a b
  | `(nlexpr| sub($a, $b)) =>
    arithmetic env stx .sub a b
  | `(nlexpr| eq($a, $b)) =>
    let (ta, a) ← expression env a
    let (tb, b) ← expression env b
    if ta.isBytes || tb.isBytes then throwErrorAt stx "Bytes32 equality is not supported"
    let ty ← commonType stx ta tb
    let a ← coerceExpression stx ta ty a
    let b ← coerceExpression stx tb ty b
    pure (.bool, ← `(Nightlean.Expr.eq $a $b))
  | `(nlexpr| select($c, $a, $b)) =>
    let c ← expected env c .bool
    let (ta, a) ← expression env a
    let (tb, b) ← expression env b
    if ta.isBytes || tb.isBytes then throwErrorAt stx "Bytes32 selection is not supported"
    let ty ← commonType stx ta tb
    let a ← coerceExpression stx ta ty a
    let b ← coerceExpression stx tb ty b
    pure (ty, ← `(Nightlean.Expr.select $c $a $b))
  | `(nlexpr| poseidon2($domain:num, $a, $b)) =>
    let a ← expected env a .native
    let b ← expected env b .native
    pure (.native, ← `(Nightlean.Expr.poseidon2 $domain $a $b))
  | _ => throwErrorAt stx "unsupported Nightlean expression"
where
  expected (env : Bindings) (stx : TSyntax `nlexpr) (ty : Ty) : CommandElabM (TSyntax `term) := do
    if let .uint maximum := ty then
      if let `(nlexpr| $n:num) := stx then
        unless n.getNat ≤ maximum do throwErrorAt stx "unsigned constant exceeds its type"
        return ← `(Nightlean.Expr.uint $(natTerm maximum) $n)
    let (found, value) ← expression env stx
    coerceExpression stx found ty value
  arithmetic (env : Bindings) (stx : Syntax) (op : ScalarPolicy.Binary)
      (left right : TSyntax `nlexpr) : CommandElabM (Ty × TSyntax `term) := do
    let (lt, left) ← expression env left
    let (rt, right) ← expression env right
    let result ← match ScalarPolicy.infer op lt.scalarKind rt.scalarKind with
      | .ok result => pure result
      | .error message => throwErrorAt stx message
    match result with
    | .native =>
      let left ← coerceExpression stx lt .native left
      let right ← coerceExpression stx rt .native right
      let term ← match op with
        | .add => `(Nightlean.Expr.add $left $right)
        | .sub => `(Nightlean.Expr.sub $left $right)
        | .mul => `(Nightlean.Expr.mul $left $right)
      pure (.native, term)
    | .uint maximum =>
      let term ← match op with
        | .add => `(Nightlean.Expr.uadd $left $right)
        | .sub => `(Nightlean.Expr.usub $left $right)
        | .mul => `(Nightlean.Expr.umul $left $right)
      pure (.uint maximum, term)
    | .bool => throwErrorAt stx "invalid arithmetic result type"
    | .bytes _ => throwErrorAt stx "Bytes32 does not support arithmetic"

private def checkedExpression (env : Bindings) (stx : TSyntax `nlexpr) (ty : Ty) :
    CommandElabM (TSyntax `term) := do
  if let .uint maximum := ty then
    if let `(nlexpr| $n:num) := stx then
      unless n.getNat ≤ maximum do throwErrorAt stx "unsigned constant exceeds its type"
      return ← `(Nightlean.Expr.uint $(natTerm maximum) $n)
  let (found, value) ← expression env stx
  coerceExpression stx found ty value

private def ensureFresh (env : Bindings) (id : TSyntax `ident) : CommandElabM Unit := do
  if env.any (fun p => p.1 == id.getId.toString) then
    throwErrorAt id "duplicate Nightlean value '{id.getId}'"

private def failDisclosure (diagnostic : Diagnostic) : CommandElabM Unit :=
  throwError "{diagnostic.span.file}:{diagnostic.span.line}:{diagnostic.span.column}: {diagnostic.message}"

/-- Evaluate only the typed AST definitions constructed by these elaborators. -/
private unsafe def checkGeneratedCircuit (name : Name) : CommandElabM Unit := do
  let value ← evalConstCheck Circuit ``Circuit name
  match Disclosure.circuit value with
  | .ok _ => pure ()
  | .error diagnostic => failDisclosure diagnostic

private unsafe def checkGeneratedContract (name : Name) : CommandElabM Unit := do
  let value ← evalConstCheck Contract ``Contract name
  match Disclosure.contract value with
  | .ok _ => pure ()
  | .error diagnostic => failDisclosure diagnostic

@[command_elab circuitCommand] def elabCircuit : CommandElab := fun stx => do
  match stx with
  | `(nightlean_circuit $name:ident where $stmts:nlcstmt* end) =>
    let mut env : Bindings := []
    let mut inputs : Array (TSyntax `term) := #[]
    let mut inputInfo := []
    let mut publicInputInfo := []
    let mut outputs : Array (TSyntax `term) := #[]
    let mut outputInfo : List (String × Ty) := []
    let mut constraints : Array (TSyntax `term) := #[]
    for stmt in stmts do
      match stmt with
      | `(nlcstmt| public $id:ident : $ty:nltype)
      | `(nlcstmt| private $id:ident : $ty:nltype) =>
        ensureFresh env id
        let t ← readTy ty
        let tt ← tyTerm t
        let isPublic := stmt.raw[0].getAtomVal == "public"
        let visibility ← if isPublic then `(Nightlean.Visibility.public) else `(Nightlean.Visibility.private)
        let span ← spanTerm stmt
        inputs := inputs.push (← `({ name := $(stringTerm id.getId.toString), ty := $tt, visibility := $visibility, span := $span : Nightlean.Input }))
        env := (id.getId.toString, t, ← `(@Nightlean.Expr.ref $tt $(stringTerm id.getId.toString))) :: env
        inputInfo := inputInfo ++ [(id.getId.toString, t)]
        if isPublic then publicInputInfo := publicInputInfo ++ [(id.getId.toString, t)]
      | `(nlcstmt| let $id:ident : $ty:nltype := $value:nlexpr) =>
        ensureFresh env id
        let t ← readTy ty
        let retain := (match t with | .uint _ => Bool.true | _ => Bool.false) || hasPartialScalar value
        let value ← checkedExpression env value t
        if retain then
          -- Equality keeps partial range/underflow checks in unused bindings.
          -- Removing it requires a proof that evaluating the expression cannot reject.
          constraints := constraints.push (← `(Nightlean.Expr.eq $value $value))
        env := (id.getId.toString, t, value) :: env
      | `(nlcstmt| assert $value:nlexpr) =>
        constraints := constraints.push (← checkedExpression env value .bool)
      | `(nlcstmt| output $id:ident : $ty:nltype := $value:nlexpr) =>
        if outputInfo.any (fun p => p.1 == id.getId.toString) || inputInfo.any (fun p => p.1 == id.getId.toString) then
          throwErrorAt id "duplicate Nightlean output '{id.getId}'"
        let t ← readTy ty
        let tt ← tyTerm t
        let value ← checkedExpression env value t
        let span ← spanTerm stmt
        outputs := outputs.push (← `({ name := $(stringTerm id.getId.toString), ty := $tt, value := $value, span := $span : Nightlean.Output }))
        outputInfo := outputInfo ++ [(id.getId.toString, t)]
      | _ => throwErrorAt stmt "unsupported Nightlean circuit statement"
    let span ← spanTerm stx
    let fullName := (← getCurrNamespace) ++ name.getId
    elabCommand (← `(def $name : Nightlean.Circuit := { name := $(stringTerm fullName.toString), inputs := [$inputs,*], outputs := [$outputs,*], constraints := [$constraints,*], span := $span }))
    unsafe checkGeneratedCircuit fullName
    modifyEnv fun e => circuitRegistry.addEntry e {declName := fullName, inputs := inputInfo, publicInputs := publicInputInfo, outputs := outputInfo}
  | _ => throwUnsupportedSyntax

private def addReferences (env : Bindings) (items : List (String × Ty)) : CommandElabM Bindings := do
  let mut env := env
  for (name, ty) in items do
    if env.any (fun p => p.1 == name) then throwError "ambiguous circuit input/output '{name}'"
    env := (name, ty, ← `(@Nightlean.Expr.ref $(← tyTerm ty) $(stringTerm name))) :: env
  pure env

private def addReferenceAs (env : Bindings) (sourceName internalName : String) (ty : Ty) :
    CommandElabM Bindings := do
  pure ((sourceName, ty, ← `(@Nightlean.Expr.ref $(← tyTerm ty) $(stringTerm internalName))) :: env)

private structure EntryEffects where
  env : Bindings
  terms : Array (TSyntax `term) := #[]
  spans : Array (TSyntax `term) := #[]
  guards : Array (TSyntax `term) := #[]
  nextLocal : Nat := 0
  usedLocalNames : List String := []

private def explicitEffectGuard (effect : TSyntax `nleffect) : Option (TSyntax `nlexpr) :=
  match effect with
  | `(nleffect| when $condition:nlexpr write $_state:ident := $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr insert $_state:ident [ $_key:nlexpr ] := $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr require $_value:nlexpr) => some condition
  | `(nleffect| when $condition:nlexpr read $_state:ident as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr read $_state:ident [ $_key:nlexpr ] as $_dest:ident) => some condition
  | `(nleffect| when $condition:nlexpr member $_state:ident [ $_key:nlexpr ] as $_dest:ident) => some condition
  | _ => none

private def effectGuardTerm (env : Bindings) (parent : Option (TSyntax `term))
    (effect : TSyntax `nleffect) : CommandElabM (TSyntax `term) := do
  let explicit ← match explicitEffectGuard effect with
    | none => pure none
    | some condition => pure (some (← checkedExpression env condition .bool))
  match parent, explicit with
  | none, none => `(none)
  | none, some condition => `(some $condition)
  | some parent, none => `(some $parent)
  | some parent, some condition =>
    `(some (Nightlean.Backend.Impact.activityGuardWithin $parent $condition))

private def chooseBranchLocalName (env : Bindings) (used : List String) (next : Nat) :
    String × Nat := Id.run do
  let mut candidateIndex := next
  let mut candidate := s!"nightlean_if_local_{candidateIndex}"
  while env.any (fun binding => binding.1 == candidate) || used.contains candidate do
    candidateIndex := candidateIndex + 1
    candidate := s!"nightlean_if_local_{candidateIndex}"
  return (candidate, candidateIndex + 1)

private partial def syntaxIdentifiers : Syntax → List String
  | .ident _ _ name _ => [name.toString]
  | .node _ _ arguments => arguments.toList.flatMap syntaxIdentifiers
  | _ => []

private def freshReadName (depth : Nat) (state : EntryEffects) (destination : TSyntax `ident) :
    CommandElabM (String × EntryEffects) := do
  ensureFresh state.env destination
  let sourceName := destination.getId.toString
  if depth == 0 then return (sourceName, state)
  let (internalName, nextLocal) :=
    chooseBranchLocalName state.env state.usedLocalNames state.nextLocal
  return (internalName, {state with nextLocal, usedLocalNames := internalName :: state.usedLocalNames})

private def bindReadName (state : EntryEffects) (sourceName internalName : String) (ty : Ty) :
    CommandElabM EntryEffects := do
  let env ← if sourceName == internalName then addReferences state.env [(sourceName, ty)]
    else addReferenceAs state.env sourceName internalName ty
  pure {state with env}

private def elaborateEffect (schema : List (String × StateKind))
    (parent : Option (TSyntax `term)) (depth : Nat) (state : EntryEffects)
    (effect : TSyntax `nleffect) : CommandElabM EntryEffects := do
  let guard ← effectGuardTerm state.env parent effect
  let span ← spanTerm effect
  let mut state := {state with
    spans := state.spans.push span
    guards := state.guards.push guard}
  match effect with
  | `(nleffect| require $value:nlexpr) =>
    let condition ← checkedExpression state.env value .bool
    let term ← `(Nightlean.Effect.require $condition)
    state := {state with terms := state.terms.push term}
  | `(nleffect| when $_:nlexpr require $value:nlexpr) =>
    let condition ← checkedExpression state.env value .bool
    let term ← `(Nightlean.Effect.require $condition)
    state := {state with terms := state.terms.push term}
  | `(nleffect| when $_:nlexpr read $storage:ident as $destination:ident)
  | `(nleffect| read $storage:ident as $destination:ident) => do
    let some (.cell ty) := schema.lookup storage.getId.toString
      | throwErrorAt storage "read requires a declared state cell"
    let (readName, updated) ← freshReadName depth state destination
    let term ← `(Nightlean.Effect.readCell
      $(stringTerm storage.getId.toString) $(stringTerm readName) $(← tyTerm ty))
    state := {updated with terms := updated.terms.push term}
    state ← bindReadName state destination.getId.toString readName ty
  | `(nleffect| when $_:nlexpr read $storage:ident [ $key:nlexpr ] as $destination:ident)
  | `(nleffect| read $storage:ident [ $key:nlexpr ] as $destination:ident) => do
    let some (.map keyTy valueTy) := schema.lookup storage.getId.toString
      | throwErrorAt storage "map read requires a declared state map"
    let (readName, updated) ← freshReadName depth state destination
    let loweredKey ← checkedExpression updated.env key keyTy
    let term ← `(Nightlean.Effect.readMap
      $(stringTerm storage.getId.toString) $(stringTerm readName)
      $(← tyTerm keyTy) $(← tyTerm valueTy) $loweredKey)
    state := {updated with terms := updated.terms.push term}
    state ← bindReadName state destination.getId.toString readName valueTy
  | `(nleffect| when $_:nlexpr member $storage:ident [ $key:nlexpr ] as $destination:ident)
  | `(nleffect| member $storage:ident [ $key:nlexpr ] as $destination:ident) => do
    let some (.map keyTy valueTy) := schema.lookup storage.getId.toString
      | throwErrorAt storage "membership requires a declared state map"
    let (readName, updated) ← freshReadName depth state destination
    let loweredKey ← checkedExpression updated.env key keyTy
    let term ← `(Nightlean.Effect.readMember
      $(stringTerm storage.getId.toString) $(stringTerm readName)
      $(← tyTerm keyTy) $(← tyTerm valueTy) $loweredKey)
    state := {updated with terms := updated.terms.push term}
    state ← bindReadName state destination.getId.toString readName .bool
  | `(nleffect| write $storage:ident := $value:nlexpr)
  | `(nleffect| when $_:nlexpr write $storage:ident := $value:nlexpr) => do
    let some (.cell ty) := schema.lookup storage.getId.toString
      | throwErrorAt storage "write requires a declared state cell"
    let loweredValue ← checkedExpression state.env value ty
    let term ← `(Nightlean.Effect.writeCell
      $(stringTerm storage.getId.toString) $(← tyTerm ty) $loweredValue)
    state := {state with terms := state.terms.push term}
  | `(nleffect| insert $storage:ident [ $key:nlexpr ] := $value:nlexpr)
  | `(nleffect| when $_:nlexpr insert $storage:ident [ $key:nlexpr ] := $value:nlexpr) => do
    let some (.map keyTy valueTy) := schema.lookup storage.getId.toString
      | throwErrorAt storage "insert requires a declared state map"
    let loweredKey ← checkedExpression state.env key keyTy
    let loweredValue ← checkedExpression state.env value valueTy
    let term ← `(Nightlean.Effect.writeMap
      $(stringTerm storage.getId.toString) $(← tyTerm keyTy) $(← tyTerm valueTy)
      $loweredKey $loweredValue)
    state := {state with terms := state.terms.push term}
  | `(nleffect| absent $storage:ident [ $key:nlexpr ]) => do
    if depth > 0 then throwErrorAt effect "absent queries inside if/else blocks are unsupported"
    let some (.map keyTy _) := schema.lookup storage.getId.toString
      | throwErrorAt storage "absent requires a declared state map"
    let loweredKey ← checkedExpression state.env key keyTy
    let term ← `(Nightlean.Effect.requireAbsent
      $(stringTerm storage.getId.toString) $(← tyTerm keyTy) $loweredKey)
    state := {state with terms := state.terms.push term}
  | _ => throwErrorAt effect "unsupported Nightlean state effect"
  pure state

private partial def elaborateStatements (schema : List (String × StateKind))
    (parent : Option (TSyntax `term)) (depth : Nat)
    (statements : Array (TSyntax `nlstatement)) (initial : EntryEffects) :
    CommandElabM EntryEffects := do
  let mut state := initial
  for statement in statements do
    match statement with
    | `(nlstatement| $effect:nleffect) =>
      state ← elaborateEffect schema parent depth state effect
    | `(nlstatement| if $condition:nlexpr then { $thenStatements:nlstatement* }
        else { $elseStatements:nlstatement* }) => do
      let condition ← checkedExpression state.env condition .bool
      let parentExpression ← match parent with
        | some expression => pure expression
        | none => `(Nightlean.Expr.bool Bool.true)
      let thenPath : Option (TSyntax `term) := some (←
        `(Nightlean.Backend.Impact.activityGuardWithin
          $parentExpression $condition))
      let negated ← `(Nightlean.Expr.eq $condition (Nightlean.Expr.bool Bool.false))
      let elsePath : Option (TSyntax `term) := some (←
        `(Nightlean.Backend.Impact.activityGuardWithin
          $parentExpression $negated))
      let branchEnv := state.env
      let afterThen ← elaborateStatements schema thenPath (depth + 1) thenStatements state
      let afterElse ← elaborateStatements schema elsePath (depth + 1) elseStatements
        {afterThen with env := branchEnv}
      state := {afterElse with env := branchEnv}
    | _ => throwErrorAt statement "unsupported Nightlean state statement"
  pure state

@[command_elab contractCommand] def elabContract : CommandElab := fun stx => do
  match stx with
  | `(nightlean_contract $name:ident where $states:nlstate* $entries:nlentry* end) =>
    let mut stateTerms : Array (TSyntax `term) := #[]
    let mut schema : List (String × StateKind) := []
    for state in states do
      let (id, kind, term) ← match state with
        | `(nlstate| cell $id:ident : $ty:nltype) => do
          let t ← readTy ty
          pure (id, StateKind.cell t, ← `(Nightlean.StateKind.cell $(← tyTerm t)))
        | `(nlstate| map $id:ident : $key:nltype => $value:nltype) => do
          let k ← readTy key
          let v ← readTy value
          pure (id, StateKind.map k v, ← `(Nightlean.StateKind.map $(← tyTerm k) $(← tyTerm v)))
        | _ => throwErrorAt state "unsupported Nightlean state declaration"
      if schema.any (fun p => p.1 == id.getId.toString) then throwErrorAt id "duplicate Nightlean state"
      schema := schema ++ [(id.getId.toString, kind)]
      stateTerms := stateTerms.push (← `({ name := $(stringTerm id.getId.toString), kind := $term, span := $(← spanTerm state) : Nightlean.StateDecl }))
    let mut entryTerms : Array (TSyntax `term) := #[]
    let mut entryNames : List Name := []
    for entryStx in entries do
      match entryStx with
      | `(nlentry| entry $id:ident uses $circuit:ident where $statements:nlstatement* end) =>
        if entryNames.contains id.getId then throwErrorAt id "duplicate Nightlean entrypoint"
        entryNames := id.getId :: entryNames
        let registry := circuitRegistry.getState (← getEnv)
        let fullName := (← getCurrNamespace) ++ circuit.getId
        let some info := registry.find? (fun i => i.declName == fullName || i.declName == circuit.getId)
          | throwErrorAt circuit "entrypoint requires a registered Nightlean circuit"
        let env ← addReferences [] (info.inputs ++ info.outputs)
        let reserved := statements.toList.flatMap (fun statement => syntaxIdentifiers statement.raw)
        let initial : EntryEffects := {env, usedLocalNames := reserved}
        let lowered ← elaborateStatements schema none 0 statements initial
        let circuitTerm := mkIdent info.declName
        entryTerms := entryTerms.push (← `({ name := $(stringTerm id.getId.toString), circuit := $circuitTerm, effects := [$lowered.terms,*], span := $(← spanTerm entryStx), effectSpans := [$lowered.spans,*], effectGuards := [$lowered.guards,*] : Nightlean.Entrypoint }))
      | _ => throwErrorAt entryStx "unsupported Nightlean entrypoint"
    let span ← spanTerm stx
    let fullName := (← getCurrNamespace) ++ name.getId
    elabCommand (← `(def $name : Nightlean.Contract := {name := $(stringTerm fullName.toString), state := [$stateTerms,*], entrypoints := [$entryTerms,*], span := $span }))
    unsafe checkGeneratedContract fullName
    modifyEnv fun e => contractRegistry.addEntry e fullName
  | _ => throwUnsupportedSyntax

/-- Structured source declarations support forward references and lexical IDs.
The generated value enters exactly the same circuit registry and compiler. -/
scoped syntax (name := helperCircuitCommand) "nightlean_helper_circuit" ident
  "from" ident "entry" str : command

open scoped Nightlean

@[command_elab helperCircuitCommand] unsafe def elabHelperCircuit : CommandElab := fun stx => do
  match stx with
  | `(nightlean_helper_circuit $name:ident from $source:ident entry $exportName:str) =>
    let namespaceName := (← getCurrNamespace) ++ source.getId
    let sourceName := if (← getEnv).contains namespaceName then namespaceName else source.getId
    let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
    match ComponentDisclosure.checkProgram program exportName.getString with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let value ← match Helpers.compile program exportName.getString with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "helper compilation failed"
    let fullName := (← getCurrNamespace) ++ name.getId
    let sourceTerm := mkIdent sourceName
    elabCommand (← `(def $name : Nightlean.Circuit :=
      match Nightlean.Helpers.compile $sourceTerm $exportName with
      | .ok value => {value with name := $(stringTerm fullName.toString)}
      | .error _ => {name := $(stringTerm fullName.toString)}))
    checkGeneratedCircuit fullName
    modifyEnv fun env => circuitRegistry.addEntry env {
      declName := fullName
      inputs := value.inputs.map fun input => (input.name, input.ty)
      publicInputs := (value.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty)
      outputs := value.outputs.map fun item => (item.name, item.ty)
      sourceProgram? := some (sourceName, exportName.getString)
    }
  | _ => throwUnsupportedSyntax

/-- Compile a generic source export into one registered monomorphic helper program.
The compiler later checks this generated concrete program again. -/
scoped syntax (name := genericHelperCircuitCommand) "nightlean_generic_circuit" ident
  "from" ident "entry" str : command

open scoped Nightlean

@[command_elab genericHelperCircuitCommand] unsafe def elabGenericHelperCircuit : CommandElab := fun stx => do
  match stx with
  | `(nightlean_generic_circuit $name:ident from $source:ident entry $exportName:str) => do
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    let sourceProgram ← evalConstCheck Helpers.Specialization.Program
      ``Helpers.Specialization.Program sourceName
    let specialized ← match Helpers.Specialization.specialize sourceProgram exportName.getString with
      | .ok result => pure result
      | .error diagnostic => failDisclosure diagnostic *> throwError "generic helper specialization failed"
    match ComponentDisclosure.checkProgram specialized.program specialized.exportName with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let value ← match Helpers.compile specialized.program specialized.exportName with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "generic helper compilation failed"
    let fullName := (← getCurrNamespace) ++ name.getId.eraseMacroScopes
    let programName := fullName ++ `specializedProgram
    if (← getEnv).contains programName then
      throwErrorAt name "generated specialized program name collides with an existing declaration"
    let sourceTerm := mkIdent sourceName
    let programIdent := mkIdent programName
    elabCommand (← `(def $programIdent : Nightlean.Helpers.Program :=
      match Nightlean.Helpers.Specialization.specialize $sourceTerm $exportName with
      | .ok result => result.program
      | .error _ => {}))
    let programTerm := mkIdent programName
    elabCommand (← `(def $name : Nightlean.Circuit :=
      match Nightlean.Helpers.compile $programTerm $exportName with
      | .ok value => {value with name := $(stringTerm fullName.toString)}
      | .error _ => {name := $(stringTerm fullName.toString)}))
    checkGeneratedCircuit fullName
    let signatureText := (Lean.toJson specialized.signatureArtifact).pretty
    modifyEnv fun env => circuitRegistry.addEntry env {
      declName := fullName
      inputs := value.inputs.map fun input => (input.name, input.ty)
      publicInputs := (value.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty)
      outputs := value.outputs.map fun item => (item.name, item.ty)
      sourceProgram? := some (programName, specialized.exportName)
      specializationArtifact? := some signatureText
    }
  | _ => throwUnsupportedSyntax

/-- Explicit source spelling for component-aware helper circuits. It compiles
through the same checked helper IR and mandatory origin pass. -/
scoped syntax (name := componentCircuitCommand) "nightlean_component_circuit" ident
  "from" ident "entry" str : command

@[command_elab componentCircuitCommand] unsafe def elabComponentCircuit : CommandElab := fun stx => do
  match stx with
  | `(nightlean_component_circuit $name:ident from $source:ident entry $exportName:str) =>
    elabHelperCircuit (← `(command| nightlean_helper_circuit $name from $source entry $exportName))
  | _ => throwUnsupportedSyntax

/-- Portable host-only execution plans never enter the native circuit registry. -/
scoped syntax (name := controlPlanCommand) "nightlean_control" ident
  "from" ident "entry" str : command

open scoped Nightlean

@[command_elab controlPlanCommand] unsafe def elabControlPlan : CommandElab := fun stx => do
  match stx with
  | `(nightlean_control $name:ident from $source:ident entry $exportName:str) =>
    let namespaceName := (← getCurrNamespace) ++ source.getId
    let sourceName := if (← getEnv).contains namespaceName then namespaceName else source.getId
    let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
    match Control.compile program exportName.getString with
    | .error diagnostic => throwErrorAt stx diagnostic.message
    | .ok _ => pure ()
    let sourceTerm := mkIdent sourceName
    elabCommand (← `(def $name : Lean.Json :=
      match Nightlean.Control.compile $sourceTerm $exportName with
      | .ok value => value
      | .error _ => Lean.Json.null))
    let fullName := (← getCurrNamespace) ++ name.getId
    modifyEnv fun env => controlRegistry.addEntry env fullName
  | _ => throwUnsupportedSyntax

scoped syntax (name := witnessCircuitCommand) "nightlean_witness_circuit" ident
  "from" ident "entry" str : command

@[command_elab witnessCircuitCommand] unsafe def elabWitnessCircuit : CommandElab := fun stx => do
  match stx with
  | `(nightlean_witness_circuit $name:ident from $source:ident entry $exportName:str) =>
    let namespaceName := (← getCurrNamespace) ++ source.getId
    let sourceName := if (← getEnv).contains namespaceName then namespaceName else source.getId
    let program ← evalConstCheck Helpers.Program ``Helpers.Program sourceName
    let fullName := (← getCurrNamespace) ++ name.getId
    let compiled ← match Witness.compile program exportName.getString fullName.toString with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "typed witness compilation failed"
    let sourceTerm := mkIdent sourceName
    let fullNameTerm := stringTerm fullName.toString
    elabCommand (← `(def $name : Nightlean.Circuit :=
      match Nightlean.Witness.compile $sourceTerm $exportName $fullNameTerm with
      | .ok value => value.circuit
      | .error _ => {name := $fullNameTerm, inputs := [], outputs := [], constraints := []}))
    unsafe checkGeneratedCircuit fullName
    modifyEnv fun env => circuitRegistry.addEntry env {
      declName := fullName,
      inputs := compiled.circuit.inputs.map fun input => (input.name, input.ty),
      publicInputs := (compiled.circuit.inputs.filter (·.visibility == .public)).map fun input => (input.name, input.ty),
      outputs := compiled.circuit.outputs.map fun value => (value.name, value.ty),
      sourceProgram? := some (sourceName, exportName.getString)}
    modifyEnv fun env => witnessRegistry.addEntry env {circuitName := fullName, sourceName, exportName := exportName.getString}
  | _ => throwUnsupportedSyntax

private def moduleProgramDeclName (contractName : Name) (ordinal : Nat) : Name :=
  contractName ++ Name.str .anonymous ("__moduleProgram_" ++ toString ordinal)

private def moduleCircuitDeclName (contractName : Name) (outputName : String) : Name :=
  contractName ++ Name.str .anonymous "__moduleCircuit" ++ Name.str .anonymous outputName

private def moduleCapabilities : Capabilities := {
  poseidon2 := Bool.true
  stateCells := Bool.true
  stateMaps := Bool.true}

/-- Re-read every registered module definition constant before expansion. -/
unsafe def moduleRegistryForBuild : CommandElabM Modules.Registry := do
  let mut registry : Modules.Registry := {}
  for info in moduleSourceRegistry.getState (← getEnv) do
    let definition ← evalConstCheck Modules.Definition ``Modules.Definition info.definitionName
    registry ← match registry.register info.sourceName definition with
      | .ok value => pure value
      | .error diagnostic => failDisclosure diagnostic *> throwError "module registration failed"
  pure registry

/-- Re-expand a registered module root from exact source constants. This is
called by both elaboration and the compiler's mandatory source checks. -/
unsafe def rebuildModuleBuild (buildInfo : ModuleBuildInfo) : CommandElabM ModuleBuildOutput := do
  let registry ← moduleRegistryForBuild
  let request ← evalConstCheck Modules.Request ``Modules.Request buildInfo.requestName
  let expansion ← match Modules.expand registry request.sourceName request.arguments with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module expansion failed"
  let plan ← match expansion.contractPlan expansion.root with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module contract planning failed"
  let groups ← match plan.specializationGroups with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module specialization planning failed"
  let mut sources : List (Name × Helpers.Specialization.Program) := []
  for group in groups do
    let source ← evalConstCheck Helpers.Specialization.Program
      ``Helpers.Specialization.Program group.sourceProgram
    sources := sources ++ [(group.sourceProgram, source)]
  let specialized ← match plan.specializeWithSources {} sources with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module helper specialization failed"
  let mut programs : List (Name × Name × Helpers.Program) := []
  let mut ordinal := 0
  for (sourceName, batch) in specialized.batches do
    let programName := moduleProgramDeclName buildInfo.contractName ordinal
    programs := programs ++ [(sourceName, programName, batch.program)]
    ordinal := ordinal + 1
  let mut circuitInfos : List ModuleCircuitBuildInfo := []
  let mut circuitValues : List Circuit := []
  for source in plan.circuits do
    let some (_, programName, program) := programs.find? (·.1 == source.source.program)
      | throwError "module source program was not specialized"
    match ComponentDisclosure.checkProgram program source.outputName with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let circuit ← match source.kind with
      | .witness => do
        match Witness.compile program source.outputName source.outputName with
        | .ok compiled => pure compiled.circuit
        | .error diagnostic => failDisclosure diagnostic *> throwError "module witness compilation failed"
      | .circuit =>
        match Helpers.compile program source.outputName with
        | .ok compiled => pure compiled
        | .error diagnostic => failDisclosure diagnostic *> throwError "module circuit compilation failed"
      | _ => throwError "module circuit plan contains a non-circuit member"
    match Disclosure.circuit circuit with
    | .ok _ => pure ()
    | .error diagnostic => failDisclosure diagnostic
    let some (_, batch) := specialized.batches.find? (·.1 == source.source.program)
      | throwError "module specialization batch was not retained"
    let some signatureArtifact := batch.signatureArtifactFor source.outputName
      | throwError "module specialization signature is missing"
    let declarationName := moduleCircuitDeclName buildInfo.contractName source.outputName
    circuitInfos := circuitInfos ++ [{
      source
      declarationName
      programName
      program
      circuit
      signatureArtifact}]
    circuitValues := circuitValues ++ [circuit]
  let contract ← match plan.assembleContract buildInfo.contractName.toString circuitValues with
    | .ok value => pure value
    | .error diagnostic => failDisclosure diagnostic *> throwError "module contract assembly failed"
  match contract.validate moduleCapabilities with
  | .ok _ => pure ()
  | .error diagnostic => failDisclosure diagnostic
  match Disclosure.contract contract with
  | .ok _ => pure ()
  | .error diagnostic => failDisclosure diagnostic
  pure {specialized, contract, programs, circuits := circuitInfos}

private partial def nameTerm : Name → CommandElabM (TSyntax `term)
  | .anonymous => `(Lean.Name.anonymous)
  | .str parent component => do
    let parentTerm ← nameTerm parent
    `(Lean.Name.str $parentTerm $(stringTerm component))
  | .num parent value => do
    let parentTerm ← nameTerm parent
    `(Lean.Name.num $parentTerm $(natTerm value))

private def moduleRegistryTerm : CommandElabM (TSyntax `term) := do
  let infos := moduleSourceRegistry.getState (← getEnv)
  let entries ← infos.toList.toArray.mapM fun info => do
    let sourceName ← nameTerm info.sourceName
    let definition := mkIdent info.definitionName
    `( ({sourceName := $sourceName, definition := $definition : Nightlean.Modules.Registered}) )
  let modules ← `(([$entries,*] : List Nightlean.Modules.Registered))
  `({modules := $modules : Nightlean.Modules.Registry})

private def moduleSourceProgramsTerm (specialized : Modules.SpecializedModule) :
    CommandElabM (TSyntax `term) := do
  let entries ← specialized.batches.toArray.mapM fun (sourceName, _) => do
    let sourceNameTerm ← nameTerm sourceName
    let source := mkIdent sourceName
    `(($sourceNameTerm, $source))
  `(([$entries,*] : List (Lean.Name × Nightlean.Helpers.Specialization.Program)))

private def moduleSpecializeTerm (buildInfo : ModuleBuildInfo)
    (specialized : Modules.SpecializedModule) : CommandElabM (TSyntax `term) := do
  let registry ← moduleRegistryTerm
  let request := mkIdent buildInfo.requestName
  let sources ← moduleSourceProgramsTerm specialized
  `(Nightlean.Modules.specializeRequestWithSources {} {} $registry $request $sources)

private def moduleProgramBodyTerm (specializeTerm : TSyntax `term) (sourceName : Name) :
    CommandElabM (TSyntax `term) := do
  let sourceNameTerm ← nameTerm sourceName
  `(match ($specializeTerm) with
    | .ok specialized =>
      match specialized.findBatch $sourceNameTerm with
      | some batch => batch.program
      | none => ({} : Nightlean.Helpers.Program)
    | .error _ => ({} : Nightlean.Helpers.Program))

private def moduleCircuitBodyTerm (source : Modules.ModuleCircuitSource)
    (programName : Name) : CommandElabM (TSyntax `term) := do
  let program := mkIdent programName
  let outputName := stringTerm source.outputName
  match source.kind with
  | .witness =>
    `(match Nightlean.Witness.compile $program $outputName $outputName with
      | .ok value => value.circuit
      | .error _ => {name := $outputName, inputs := [], outputs := [], constraints := []})
  | .circuit =>
    `(match Nightlean.Helpers.compile $program $outputName with
      | .ok value => value
      | .error _ => {name := $outputName, inputs := [], outputs := [], constraints := []})
  | _ => throwError "module circuit source has an invalid member kind"

scoped syntax (name := moduleSourceCommand) "nightlean_module" "from" ident : command

open scoped Nightlean

@[command_elab moduleSourceCommand] unsafe def elabModuleSource : CommandElab := fun stx => do
  match stx with
  | `(nightlean_module from $source:ident) => do
    let sourceName ← liftCoreM <| resolveGlobalConstNoOverload source
    if moduleSourceRegistry.getState (← getEnv) |>.any (·.sourceName == sourceName) then
      throwErrorAt source "Noctium module source identity is already registered"
    let definition ← evalConstCheck Modules.Definition ``Modules.Definition sourceName
    match Modules.registerDefinition sourceName definition with
    | .error diagnostic => failDisclosure diagnostic
    | .ok _ => pure ()
    modifyEnv fun env => moduleSourceRegistry.addEntry env {
      sourceName
      definitionName := sourceName}
  | _ => throwUnsupportedSyntax

scoped syntax (name := moduleContractCommand) "nightlean_module_contract" ident
  "from" ident : command

@[command_elab moduleContractCommand] unsafe def elabModuleContract : CommandElab := fun stx => do
  match stx with
  | `(nightlean_module_contract $name:ident from $requestSource:ident) => do
    let requestName ← liftCoreM <| resolveGlobalConstNoOverload requestSource
    let fullName := (← getCurrNamespace) ++ name.getId.eraseMacroScopes
    if (← getEnv).contains fullName then
      throwErrorAt name "generated module contract name collides with an existing declaration"
    let buildInfo : ModuleBuildInfo := {contractName := fullName, requestName}
    let builtModule ← rebuildModuleBuild buildInfo
    let specializeTerm ← moduleSpecializeTerm buildInfo builtModule.specialized
    for (sourceName, programName, _) in builtModule.programs do
      let programIdent := mkIdent programName
      if (← getEnv).contains programName then
        throwErrorAt name "generated module program name collides with an existing declaration"
      let body ← moduleProgramBodyTerm specializeTerm sourceName
      elabCommand (← `(def $programIdent : Nightlean.Helpers.Program := $body))
    for circuitInfo in builtModule.circuits do
      let circuitIdent := mkIdent circuitInfo.declarationName
      if (← getEnv).contains circuitInfo.declarationName then
        throwErrorAt name "generated module circuit name collides with an existing declaration"
      let body ← moduleCircuitBodyTerm circuitInfo.source circuitInfo.programName
      elabCommand (← `(def $circuitIdent : Nightlean.Circuit := $body))
      unsafe checkGeneratedCircuit circuitInfo.declarationName
      let signatureText := (Lean.toJson circuitInfo.signatureArtifact).pretty
      modifyEnv fun env => circuitRegistry.addEntry env {
        declName := circuitInfo.declarationName
        inputs := circuitInfo.circuit.inputs.map fun input => (input.name, input.ty)
        publicInputs := (circuitInfo.circuit.inputs.filter (·.visibility == .public)).map
          fun input => (input.name, input.ty)
        outputs := circuitInfo.circuit.outputs.map fun item => (item.name, item.ty)
        sourceProgram? := some (circuitInfo.programName, circuitInfo.source.outputName)
        specializationArtifact? := some signatureText}
      if circuitInfo.source.kind == .witness then
        modifyEnv fun env => witnessRegistry.addEntry env {
          circuitName := Name.str .anonymous circuitInfo.source.outputName
          sourceName := circuitInfo.programName
          exportName := circuitInfo.source.outputName}
    let circuitTerms := builtModule.circuits.toArray.map fun circuitInfo => mkIdent circuitInfo.declarationName
    let contractNameText := stringTerm fullName.toString
    let contractIdent := mkIdent fullName
    let contractBody ← `(match ($specializeTerm) with
      | .ok specialized =>
        match specialized.plan.assembleContract $contractNameText [$circuitTerms,*] with
        | .ok contract => contract
        | .error _ => {name := $contractNameText : Nightlean.Contract}
      | .error _ => {name := $contractNameText : Nightlean.Contract})
    elabCommand (← `(def $contractIdent : Nightlean.Contract := $contractBody))
    unsafe checkGeneratedContract fullName
    modifyEnv fun env => contractRegistry.addEntry env fullName
    modifyEnv fun env => moduleBuildRegistry.addEntry env buildInfo
  | _ => throwUnsupportedSyntax

end Nightlean
