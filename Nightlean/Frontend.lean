import Nightlean.IR
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

declare_syntax_cat nltype
scoped syntax "Native" : nltype
scoped syntax "Bool" : nltype

declare_syntax_cat nlexpr
scoped syntax ident : nlexpr
scoped syntax num : nlexpr
scoped syntax "true" : nlexpr
scoped syntax "false" : nlexpr
scoped syntax "add(" nlexpr "," nlexpr ")" : nlexpr
scoped syntax "mul(" nlexpr "," nlexpr ")" : nlexpr
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
  | _ => throwErrorAt stx "unsupported Nightlean type"

private def tyTerm : Ty → CommandElabM (TSyntax `term)
  | .native => `(Nightlean.Ty.native)
  | .bool => `(Nightlean.Ty.bool)

private def stringTerm (value : String) : TSyntax `term := ⟨Syntax.mkStrLit value⟩
private def natTerm (value : Nat) : TSyntax `term := ⟨Syntax.mkNumLit (toString value)⟩

private def spanTerm (stx : Syntax) : CommandElabM (TSyntax `term) := do
  let fileMap ← getFileMap
  let pos := fileMap.toPosition (stx.getPos?.getD 0)
  let file ← getFileName
  `({ file := $(stringTerm file), line := $(natTerm pos.line),
      column := $(natTerm (pos.column + 1)) : Nightlean.SourceSpan })

private abbrev Bindings := List (String × Ty × TSyntax `term)

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
  | `(nlexpr| add($a, $b)) =>
    let a ← expected env a .native
    let b ← expected env b .native
    pure (.native, ← `(Nightlean.Expr.add $a $b))
  | `(nlexpr| mul($a, $b)) =>
    let a ← expected env a .native
    let b ← expected env b .native
    pure (.native, ← `(Nightlean.Expr.mul $a $b))
  | `(nlexpr| eq($a, $b)) =>
    let (ty, a) ← expression env a
    let b ← expected env b ty
    pure (.bool, ← `(Nightlean.Expr.eq $a $b))
  | `(nlexpr| select($c, $a, $b)) =>
    let c ← expected env c .bool
    let (ty, a) ← expression env a
    let b ← expected env b ty
    pure (ty, ← `(Nightlean.Expr.select $c $a $b))
  | `(nlexpr| poseidon2($domain:num, $a, $b)) =>
    let a ← expected env a .native
    let b ← expected env b .native
    pure (.native, ← `(Nightlean.Expr.poseidon2 $domain $a $b))
  | _ => throwErrorAt stx "unsupported Nightlean expression"
where
  expected (env : Bindings) (stx : TSyntax `nlexpr) (ty : Ty) : CommandElabM (TSyntax `term) := do
    let (found, value) ← expression env stx
    unless found == ty do throwErrorAt stx "Nightlean expression type mismatch"
    pure value

private def checkedExpression (env : Bindings) (stx : TSyntax `nlexpr) (ty : Ty) :
    CommandElabM (TSyntax `term) := do
  let (found, value) ← expression env stx
  unless found == ty do throwErrorAt stx "Nightlean expression type mismatch"
  pure value

private def ensureFresh (env : Bindings) (id : TSyntax `ident) : CommandElabM Unit := do
  if env.any (fun p => p.1 == id.getId.toString) then
    throwErrorAt id "duplicate Nightlean value '{id.getId}'"

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
        let value ← checkedExpression env value t
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
        let mut env ← addReferences [] (info.publicInputs ++ info.outputs)
        let mut effectTerms : Array (TSyntax `term) := #[]
        for effect in effects do
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
        entryTerms := entryTerms.push (← `({ name := $(stringTerm id.getId.toString), circuit := $circuitTerm, effects := [$effectTerms,*], span := $(← spanTerm entryStx) : Nightlean.Entrypoint }))
      | _ => throwErrorAt entryStx "unsupported Nightlean entrypoint"
    let span ← spanTerm stx
    let fullName := (← getCurrNamespace) ++ name.getId
    elabCommand (← `(def $name : Nightlean.Contract := {name := $(stringTerm fullName.toString), state := [$stateTerms,*], entrypoints := [$entryTerms,*], span := $span }))
    modifyEnv fun e => contractRegistry.addEntry e fullName
  | _ => throwUnsupportedSyntax

end Nightlean
