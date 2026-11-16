import Nightlean.Disclosure
import Nightlean.Helpers
import Nightlean.Control
import Lean

namespace Nightlean
open Lean Elab Command

/-- Declarations registered through the supported Nightlean circuit surface. -/
structure CircuitInfo where
  declName : Name
  inputs : List (String × Ty)
  publicInputs : List (String × Ty)
  outputs : List (String × Ty)
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

declare_syntax_cat nltype
scoped syntax "Native" : nltype
scoped syntax "Bool" : nltype
scoped syntax "UInt" num : nltype
scoped syntax "UIntRange" num : nltype

declare_syntax_cat nlexpr
scoped syntax ident : nlexpr
scoped syntax num : nlexpr
scoped syntax "true" : nlexpr
scoped syntax "false" : nlexpr
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
scoped syntax "require" nlexpr : nleffect
scoped syntax "absent" ident "[" nlexpr "]" : nleffect
scoped syntax "write" ident ":=" nlexpr : nleffect
scoped syntax "insert" ident "[" nlexpr "]" ":=" nlexpr : nleffect

declare_syntax_cat nlentry
scoped syntax "entry" ident "uses" ident "where" nleffect* "end" : nlentry
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
  | _ => throwErrorAt stx "unsupported Nightlean type"

private def tyTerm : Ty → CommandElabM (TSyntax `term)
  | .native => `(Nightlean.Ty.native)
  | .bool => `(Nightlean.Ty.bool)
  | .uint maximum => `(Nightlean.Ty.uint $(⟨Syntax.mkNumLit (toString maximum)⟩))

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
    let ty ← commonType stx ta tb
    let a ← coerceExpression stx ta ty a
    let b ← coerceExpression stx tb ty b
    pure (.bool, ← `(Nightlean.Expr.eq $a $b))
  | `(nlexpr| select($c, $a, $b)) =>
    let c ← expected env c .bool
    let (ta, a) ← expression env a
    let (tb, b) ← expression env b
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
      | `(nlentry| entry $id:ident uses $circuit:ident where $effects:nleffect* end) =>
        if entryNames.contains id.getId then throwErrorAt id "duplicate Nightlean entrypoint"
        entryNames := id.getId :: entryNames
        let registry := circuitRegistry.getState (← getEnv)
        let fullName := (← getCurrNamespace) ++ circuit.getId
        let some info := registry.find? (fun i => i.declName == fullName || i.declName == circuit.getId)
          | throwErrorAt circuit "entrypoint requires a registered Nightlean circuit"
        let mut env ← addReferences [] (info.inputs ++ info.outputs)
        let mut effectTerms : Array (TSyntax `term) := #[]
        let mut effectSpans : Array (TSyntax `term) := #[]
        for effect in effects do
          effectSpans := effectSpans.push (← spanTerm effect)
          match effect with
          | `(nleffect| require $value:nlexpr) =>
            effectTerms := effectTerms.push (← `(Nightlean.Effect.require $(← checkedExpression env value .bool)))
          | `(nleffect| read $state:ident as $dest:ident) =>
            let some (.cell ty) := schema.lookup state.getId.toString
              | throwErrorAt state "read requires a declared state cell"
            ensureFresh env dest
            effectTerms := effectTerms.push (← `(Nightlean.Effect.readCell
              $(stringTerm state.getId.toString) $(stringTerm dest.getId.toString) $(← tyTerm ty)))
            env ← addReferences env [(dest.getId.toString, ty)]
          | `(nleffect| write $state:ident := $value:nlexpr) =>
            let some (.cell ty) := schema.lookup state.getId.toString
              | throwErrorAt state "write requires a declared state cell"
            effectTerms := effectTerms.push (← `(Nightlean.Effect.writeCell
              $(stringTerm state.getId.toString) $(← tyTerm ty) $(← checkedExpression env value ty)))
          | `(nleffect| absent $state:ident [ $key:nlexpr ]) =>
            let some (.map kt _) := schema.lookup state.getId.toString
              | throwErrorAt state "absent requires a declared state map"
            effectTerms := effectTerms.push (← `(Nightlean.Effect.requireAbsent
              $(stringTerm state.getId.toString) $(← tyTerm kt) $(← checkedExpression env key kt)))
          | `(nleffect| insert $state:ident [ $key:nlexpr ] := $value:nlexpr) =>
            let some (.map kt vt) := schema.lookup state.getId.toString
              | throwErrorAt state "insert requires a declared state map"
            effectTerms := effectTerms.push (← `(Nightlean.Effect.writeMap
              $(stringTerm state.getId.toString) $(← tyTerm kt) $(← tyTerm vt)
              $(← checkedExpression env key kt) $(← checkedExpression env value vt)))
          | _ => throwErrorAt effect "unsupported Nightlean state effect"
        let circuitTerm := mkIdent info.declName
        entryTerms := entryTerms.push (← `({ name := $(stringTerm id.getId.toString), circuit := $circuitTerm, effects := [$effectTerms,*], span := $(← spanTerm entryStx), effectSpans := [$effectSpans,*] : Nightlean.Entrypoint }))
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
    }
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

end Nightlean
