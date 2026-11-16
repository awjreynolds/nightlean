import Nightlean.Field

namespace Nightlean

structure SourceSpan where
  file : String := ""
  line : Nat := 1
  column : Nat := 1
  deriving Repr, BEq, Inhabited

inductive Ty where
  | native | bool
  deriving Repr, BEq, DecidableEq, Inhabited

inductive Visibility where
  | «public» | «private»
  deriving Repr, BEq, DecidableEq, Inhabited

/-- Every expression carries its result type, independently of a backend. -/
inductive Expr : Ty → Type where
  | native (value : Nat) : Expr .native
  | bool (value : Bool) : Expr .bool
  | ref (name : String) : Expr ty
  | add (a b : Expr .native) : Expr .native
  | mul (a b : Expr .native) : Expr .native
  | eq (a b : Expr ty) : Expr .bool
  | select (condition : Expr .bool) (yes no : Expr ty) : Expr ty
  | poseidon2 (domain : Nat) (a b : Expr .native) : Expr .native
  deriving Repr

structure Input where
  name : String
  ty : Ty
  visibility : Visibility
  span : SourceSpan := {}
  deriving Repr

structure Output where
  name : String
  ty : Ty
  value : Expr ty
  span : SourceSpan := {}
  deriving Repr

structure Circuit where
  name : String
  inputs : List Input := []
  outputs : List Output := []
  constraints : List (Expr .bool) := []
  span : SourceSpan := {}
  deriving Repr

inductive StateKind where
  | cell (valueTy : Ty)
  | map (keyTy valueTy : Ty)
  deriving Repr, BEq, DecidableEq

structure StateDecl where
  name : String
  kind : StateKind
  span : SourceSpan := {}
  deriving Repr

/-- State effects are ordered transaction instructions, not circuit nodes.
A read binds a typed name for later guards/writes. Outputs are bound explicitly
by an entrypoint. The backend must bind these values into the accepted transcript. -/
inductive Effect where
  | readCell (state destination : String) (ty : Ty)
  | readMap (state destination : String) (keyTy valueTy : Ty) (key : Expr keyTy)
  | require (condition : Expr .bool)
  | writeCell (state : String) (ty : Ty) (value : Expr ty)
  | writeMap (state : String) (keyTy valueTy : Ty) (key : Expr keyTy) (value : Expr valueTy)
  | requireAbsent (state : String) (keyTy : Ty) (key : Expr keyTy)
  deriving Repr

structure Entrypoint where
  name : String
  circuit : Circuit
  effects : List Effect := []
  span : SourceSpan := {}
  deriving Repr

structure Contract where
  name : String
  state : List StateDecl := []
  entrypoints : List Entrypoint := []
  span : SourceSpan := {}
  deriving Repr

structure Capabilities where
  nativeModulus : Nat := Field.modulus
  nativeArithmetic : Bool := true
  equality : Bool := true
  select : Bool := true
  poseidon2 : Bool := false
  stateCells : Bool := false
  stateMaps : Bool := false
  deriving Repr

structure Diagnostic where
  span : SourceSpan
  message : String
  deriving Repr

abbrev TypeEnv := List (String × Ty)

def Expr.validate (caps : Capabilities) (env : TypeEnv) : Expr ty → Except String Unit
  | .native value =>
    if value < caps.nativeModulus then pure () else .error "noncanonical native constant"
  | .bool _ => pure ()
  | .ref name =>
    match env.lookup name with
    | none => .error s!"unknown reference '{name}'"
    | some found => if found == ty then pure () else .error s!"type mismatch for '{name}'"
  | .add a b | .mul a b => do
    if !caps.nativeArithmetic then throw "target lacks native arithmetic"
    a.validate caps env
    b.validate caps env
  | .eq a b => do
    if !caps.equality then throw "target lacks equality"
    a.validate caps env
    b.validate caps env
  | .select c a b => do
    if !caps.select then throw "target lacks conditional selection"
    c.validate caps env
    a.validate caps env
    b.validate caps env
  | .poseidon2 domain a b => do
    if domain >= caps.nativeModulus then throw "noncanonical Poseidon domain"
    if !caps.poseidon2 then throw "target lacks qualified Poseidon support"
    a.validate caps env
    b.validate caps env

def uniqueNames (names : List String) : Bool := names.eraseDups.length == names.length

def Circuit.validate (caps : Capabilities) (c : Circuit) : Except Diagnostic Unit := do
  if !uniqueNames (c.inputs.map (·.name)) then
    throw {span := c.span, message := "duplicate circuit input"}
  if !uniqueNames (c.outputs.map (·.name)) then
    throw {span := c.span, message := "duplicate circuit output"}
  let env := c.inputs.map fun i => (i.name, i.ty)
  for condition in c.constraints do
    match condition.validate caps env with
    | .error message => throw {span := c.span, message}
    | .ok _ => pure ()
  for output in c.outputs do
    if (env.lookup output.name).isSome then
      throw {span := output.span, message := s!"output '{output.name}' shadows a circuit input"}
    match output.value.validate caps env with
    | .error message => throw {span := output.span, message}
    | .ok _ => pure ()

private def requireState (decls : List StateDecl) (name : String) (kind : StateKind) : Except String Unit :=
  match decls.find? (·.name == name) with
  | none => .error s!"unknown state '{name}'"
  | some decl => if decl.kind == kind then pure () else .error s!"state type mismatch for '{name}'"

/-- Validate state names, typed reads, guards and writes in execution order. -/
def Entrypoint.validate (caps : Capabilities) (decls : List StateDecl) (e : Entrypoint) : Except Diagnostic Unit := do
  e.circuit.validate caps
  let mut env := (e.circuit.inputs.filter (·.visibility == .«public»)).map fun i => (i.name, i.ty)
  for output in e.circuit.outputs do
    if (e.circuit.inputs.find? (·.name == output.name)).isSome then
      throw {span := output.span, message := s!"output '{output.name}' shadows a circuit input"}
    env := env ++ [(output.name, output.ty)]
  for effect in e.effects do
    let result : Except String (Option (String × Ty)) := do
      match effect with
      | .readCell state destination ty =>
        if !caps.stateCells then throw "target lacks state cells"
        requireState decls state (.cell ty)
        pure (some (destination, ty))
      | .readMap state destination keyTy valueTy key =>
        if !caps.stateMaps then throw "target lacks state maps"
        requireState decls state (.map keyTy valueTy)
        key.validate caps env
        pure (some (destination, valueTy))
      | .require condition =>
        condition.validate caps env
        pure none
      | .writeCell state ty value =>
        if !caps.stateCells then throw "target lacks state cells"
        requireState decls state (.cell ty)
        value.validate caps env
        pure none
      | .writeMap state keyTy valueTy key value =>
        if !caps.stateMaps then throw "target lacks state maps"
        requireState decls state (.map keyTy valueTy)
        key.validate caps env
        value.validate caps env
        pure none
      | .requireAbsent state keyTy key =>
        if !caps.stateMaps then throw "target lacks state maps"
        match decls.find? (·.name == state) with
        | some {kind := .map found _, ..} =>
          if found != keyTy then throw s!"state key type mismatch for '{state}'"
        | _ => throw s!"unknown map state '{state}'"
        key.validate caps env
        pure none
    match result with
    | .error message => throw {span := e.span, message}
    | .ok none => pure ()
    | .ok (some (name, ty)) =>
      if (env.lookup name).isSome then
        throw {span := e.span, message := s!"state read shadows '{name}'"}
      env := env ++ [(name, ty)]

def Contract.validate (caps : Capabilities) (c : Contract) : Except Diagnostic Unit := do
  if !uniqueNames (c.state.map (·.name)) then
    throw {span := c.span, message := "duplicate state declaration"}
  if !uniqueNames (c.entrypoints.map (·.name)) then
    throw {span := c.span, message := "duplicate contract entrypoint"}
  for entry in c.entrypoints do entry.validate caps c.state

end Nightlean
