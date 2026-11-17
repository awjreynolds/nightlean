import Nightlean.Core
import Nightlean.Types.Composite

namespace Nightlean

inductive Visibility where
  | «public» | «private»
  deriving Repr, BEq, DecidableEq, Inhabited

inductive PrivateOriginKind where
  | parameter | provider | privateState
  deriving Repr, BEq, DecidableEq

/-- Every expression carries its result type, independently of a backend. -/
inductive Expr : Ty → Type where
  | native (value : Nat) : Expr .native
  | bool (value : Bool) : Expr .bool
  | uint (maximum value : Nat) : Expr (.uint maximum)
  /-- Pack one field-sized chunk of a typed byte string using the pinned
  little-endian chunk encoding. This constructor is for backend transcript
  lowering. Source expressions cannot cast or do arithmetic on byte strings. -/
  | bytesField (value : Expr (.bytes length)) (chunkIndex : Nat) : Expr .native
  | bytesAt (value : Expr (.bytes length)) (index : Nat) : Expr (.uint 255)
  /-- SHA-256 over the pinned FAB Bytes32 alignment, using native ZKIR
  persistent_hash and returning a typed Bytes32 digest. -/
  | persistentHash32 (value : Expr (.bytes 32)) : Expr (.bytes 32)
  /-- A canonical source-time Bytes32 value. The frontend pads UTF-8 bytes on
  the right and validation checks the resulting 32 byte values. -/
  | bytes32Literal (values : List Nat) : Expr (.bytes 32)
  /-- SHA-256 over an ordered, bounded vector of FAB-aligned Bytes32 values. -/
  | persistentHashVector32 (values : List (Expr (.bytes 32))) : Expr (.bytes 32)
  /-- SHA-256 over the canonical 32-byte little-endian Native field encoding. -/
  | persistentHashNative (value : Expr .native) : Expr (.bytes 32)
  /-- SHA-256 over an ordered vector of canonical Native field encodings. -/
  | persistentHashNativeVector (values : List (Expr .native)) : Expr (.bytes 32)
  /-- Explicitly reduce a Native field into the Jubjub scalar field. -/
  | jubjubScalarFromNative (value : Expr .native) : Expr .jubjubScalar
  /-- Losslessly expose a canonical Jubjub scalar as its Native limb. -/
  | jubjubScalarToNative (value : Expr .jubjubScalar) : Expr .native
  | jubjubMulGenerator (scalar : Expr .jubjubScalar) : Expr .jubjubPoint
  | jubjubMul (point : Expr .jubjubPoint) (scalar : Expr .jubjubScalar) : Expr .jubjubPoint
  | jubjubAdd (left right : Expr .jubjubPoint) : Expr .jubjubPoint
  | jubjubNeg (point : Expr .jubjubPoint) : Expr .jubjubPoint
  | jubjubCoordinate (point : Expr .jubjubPoint) (index : Nat) : Expr .native
  | jubjubFromCoordinates (x y : Expr .native) : Expr .jubjubPoint
  | ref (name : String) : Expr ty
  | add (a b : Expr .native) : Expr .native
  | mul (a b : Expr .native) : Expr .native
  | sub (a b : Expr .native) : Expr .native
  | uadd (a : Expr (.uint m)) (b : Expr (.uint n)) : Expr (.uint (m + n))
  | usub (a : Expr (.uint m)) (b : Expr (.uint n)) : Expr (.uint m)
  | umul (a : Expr (.uint m)) (b : Expr (.uint n)) : Expr (.uint (m * n))
  /-- Multiplicative inverse in the source type's pinned prime field. -/
  | inv (value : Expr ty) : Expr ty
  | cast (target : Ty) (value : Expr source) : Expr target
  | letE (name : String) (value : Expr source) (body : Expr ty) : Expr ty
  | assertE (condition : Expr .bool) (body : Expr ty) : Expr ty
  | disclose (span : SourceSpan) (value : Expr ty) : Expr ty
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

/-- Native scalar leaves for one source input. Byte leaves keep source byte
order and receive explicit range-constrained identifiers. -/
def Input.nativeIdentifiers (input : Input) : List String :=
  match input.ty with
  | .bytes length => (List.range length).map fun index =>
      s!"%input_{input.name}_byte_{index}"
  | .jubjubPoint => [s!"%input_{input.name}_x", s!"%input_{input.name}_y"]
  | _ => ["%input_" ++ input.name]

/-- Reserved Native projections used by the public transcript prologue for
opaque Jubjub inputs. These names never replace the typed source alias. -/
def Input.publicProjectionIdentifiers (input : Input) : List String :=
  if input.visibility != .«public» then [] else
  match input.ty with
  | .jubjubScalar => [s!"_nightlean_jubjub_scalar_{input.name}"]
  | .jubjubPoint => [s!"_nightlean_jubjub_point_{input.name}_0",
      s!"_nightlean_jubjub_point_{input.name}_1"]
  | _ => []

structure Output where
  name : String
  ty : Ty
  value : Expr ty
  span : SourceSpan := {}
  deriving Repr

/-- Recursive ledger value descriptions. Scalar leaves use the existing typed
scalar surface. Maps retain their key type and recursively describe values. -/
inductive LedgerValueType where
  | scalar (ty : Ty)
  | map (keyTy : Ty) (value : LedgerValueType)
  | composite (environment : Types.CompositeEnv) (type : Types.CompositeType)
  deriving Repr, BEq, DecidableEq

/-- A typed dynamic key in a nested ledger path. -/
inductive PathKey where
  | mk (ty : Ty) (value : Expr ty)
  deriving Repr

def PathKey.ty : PathKey → Ty
  | .mk ty _ => ty

/-- Resolve a complete source key path against a recursive map schema. -/
def LedgerValueType.resolvePath (schema : LedgerValueType) : List PathKey →
    Except String LedgerValueType
  | [] => pure schema
  | .mk keyTy _ :: rest => do
    match schema with
    | .scalar _ => throw "nested map path continues through a scalar value"
    | .map expected value =>
      unless keyTy == expected do throw "nested map key type mismatch"
      value.resolvePath rest
    | .composite .. => throw "nested map path continues through a composite value"

private def checkedNativeRecord (environment : Types.CompositeEnv)
    (type : Types.CompositeType) : Except String (Types.CheckedLayout Types.defaultLimits) := do
  let checked ← (Types.checkedLayout Types.defaultLimits environment type).mapError (·.message)
  unless checked.expandedLeaves > 0 && checked.value.nativeFieldOnly do
    throw "ledger composite values must contain one or more Native fields only"
  pure checked

def LedgerValueType.compositeSchema (schema : LedgerValueType) :
    Except String (Types.CompositeEnv × Types.CompositeType × Types.CheckedLayout Types.defaultLimits) :=
  match schema with
  | .composite environment type => do
    let checked ← checkedNativeRecord environment type
    pure (environment, type, checked)
  | _ => .error "nested map value is not a composite record"

def LedgerValueType.nativeLeafNames (environment : Types.CompositeEnv)
    (type : Types.CompositeType) : Except String (List String) := do
  let checked ← checkedNativeRecord environment type
  let rec names : Nat → Types.Layout → Except String (List String)
    | 0, _ => throw "composite leaf name traversal exhausted checked fuel"
    | fuel + 1, layout => do
      match layout with
      | .scalar .nativeField => pure ["value"]
      | .tuple items =>
        pure (← items.zipIdx.mapM fun (item, index) => do
          pure ((← names fuel item).map fun name => s!"{index}_{name}")).flatten
      | .structure _ fields =>
        pure (← fields.mapM fun (field, item) => do
          pure ((← names fuel item).map fun name =>
            if name == "value" then field else s!"{field}_{name}")).flatten
      | .vector length element =>
        pure (← (List.range length).mapM fun index => do
          pure ((← names fuel element).map fun name => s!"{index}_{name}")).flatten
      | _ => throw "ledger composite values must contain Native fields only"
  let result ← names (checked.layoutNodes + 1) checked.value
  unless result.length == checked.expandedLeaves do throw "composite leaf name count mismatch"
  pure result

structure Circuit where
  name : String
  inputs : List Input := []
  outputs : List Output := []
  constraints : List (Expr .bool) := []
  span : SourceSpan := {}
  /-- Private provenance labels for declared provider/private-state input fixtures.
  These strengthen visibility and never authorize disclosure. -/
  privateOrigins : List (String × PrivateOriginKind) := []
  deriving Repr

inductive StateKind where
  | cell (valueTy : Ty)
  | map (keyTy valueTy : Ty)
  | tree (value : LedgerValueType)
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
  | readMember (state destination : String) (keyTy valueTy : Ty) (key : Expr keyTy)
  | require (condition : Expr .bool)
  | writeCell (state : String) (ty : Ty) (value : Expr ty)
  | writeMap (state : String) (keyTy valueTy : Ty) (key : Expr keyTy) (value : Expr valueTy)
  | requireAbsent (state : String) (keyTy : Ty) (key : Expr keyTy)
  | readPath (state destination : String) (keys : List PathKey) (valueTy : Ty)
  | memberPath (state destination : String) (keys : List PathKey)
  | insertPath (state : String) (keys : List PathKey) (valueTy : Ty) (value : Expr valueTy)
  | writePath (state : String) (keys : List PathKey) (valueTy : Ty) (value : Expr valueTy)
  | readCompositePath (state destination : String) (keys : List PathKey)
      (type : Types.CompositeType) (destinations : List String)
  | writeCompositePath (state : String) (keys : List PathKey)
      (type : Types.CompositeType) (values : List (Expr .native))
  | emptyMapPath (state : String) (keys : List PathKey)
  deriving Repr

structure Entrypoint where
  name : String
  circuit : Circuit
  effects : List Effect := []
  span : SourceSpan := {}
  effectSpans : List SourceSpan := []
  /-- Optional activity guards aligned with `effects`. Scalar reads, writes,
  and require effects accept a guard. An empty list preserves legacy behavior. -/
  effectGuards : List (Option (Expr .bool)) := []
  deriving Repr

def Entrypoint.effectGuardAt (entry : Entrypoint) (index : Nat) : Option (Expr .bool) :=
  (entry.effectGuards[index]?).getD none

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
  persistentHash32 : Bool := false
  persistentHashVector32 : Bool := false
  persistentHashNative : Bool := false
  jubjub : Bool := false
  stateCells : Bool := false
  stateMaps : Bool := false
  deriving Repr

structure Diagnostic where
  span : SourceSpan
  message : String
  deriving Repr

abbrev TypeEnv := List (String × Ty)

def Ty.validate (caps : Capabilities) (ty : Ty) : Except String Unit := do
  match ty with
  | .bytes length =>
    unless length == 32 do throw "only Bytes32 is supported by this source surface"
  | .jubjubScalar | .jubjubPoint =>
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
  | .native | .bool => ScalarPolicy.validate ty.scalarKind
  | .uint maximum =>
    ScalarPolicy.validate ty.scalarKind
    unless maximum < caps.nativeModulus do throw "unsigned type exceeds native representation"

def Expr.validate (caps : Capabilities) (env : TypeEnv) : Expr ty → Except String Unit
  | .native value =>
    if value < caps.nativeModulus then pure () else .error "noncanonical native constant"
  | .uint maximum value => do
    (Ty.uint maximum).validate caps
    if value ≤ maximum then pure () else .error "unsigned constant exceeds its type"
  | .bool _ => .ok ()
  | .bytesField value chunkIndex => do
    value.validate caps env
    unless chunkIndex < 2 do throw "Bytes32 field chunk index is out of range"
  | .bytesAt value index => do
    value.validate caps env
    unless index < 32 do throw "Bytes32 byte index is out of range"
  | .persistentHash32 value => do
    unless caps.persistentHash32 do throw "target lacks qualified Bytes32 persistent-hash support"
    value.validate caps env
  | .bytes32Literal values => do
    unless values.length == 32 && values.all (· ≤ 255) do
      throw "Bytes32 literal must contain exactly 32 byte values"
  | .persistentHashVector32 values => do
    unless caps.persistentHashVector32 do throw "target lacks qualified Bytes32-vector persistent-hash support"
    unless values.length ≥ 1 && values.length ≤ 32 do
      throw "persistent hash vector must contain 1 to 32 Bytes32 values"
    for value in values do value.validate caps env
  | .persistentHashNative value => do
    unless caps.persistentHashNative do throw "target lacks qualified Native persistent-hash support"
    value.validate caps env
  | .persistentHashNativeVector values => do
    unless caps.persistentHashNative do throw "target lacks qualified Native persistent-hash support"
    unless values.length ≥ 1 && values.length ≤ 32 do
      throw "Native persistent-hash vector must contain 1 to 32 fields"
    for value in values do value.validate caps env
  | .jubjubScalarFromNative value => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    value.validate caps env
  | .jubjubScalarToNative value => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    value.validate caps env
  | .jubjubMulGenerator scalar => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    scalar.validate caps env
  | .jubjubMul point scalar => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    point.validate caps env
    scalar.validate caps env
  | .jubjubAdd left right => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    left.validate caps env
    right.validate caps env
  | .jubjubNeg point => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    point.validate caps env
  | .jubjubCoordinate point index => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    point.validate caps env
    unless index < 2 do throw "Jubjub coordinate index must be 0 or 1"
  | .jubjubFromCoordinates x y => do
    unless caps.jubjub do throw "target lacks qualified Jubjub support"
    x.validate caps env
    y.validate caps env
  | .ref name => do
    ty.validate caps
    match env.lookup name with
    | none => .error s!"unknown reference '{name}'"
    | some found => if found == ty then pure () else .error s!"type mismatch for '{name}'"
  | .add a b | .mul a b | .sub a b => do
    if !caps.nativeArithmetic then throw "target lacks native arithmetic"
    a.validate caps env
    b.validate caps env
  | .uadd a b | .usub a b | .umul a b => do
    ty.validate caps
    if !caps.nativeArithmetic then throw "target lacks native arithmetic"
    a.validate caps env
    b.validate caps env
  | .inv value => do
    match ty with
    | .native =>
      unless caps.nativeArithmetic do throw "target lacks Native inverse support"
    | .jubjubScalar =>
      unless caps.jubjub do throw "target lacks Jubjub scalar inverse support"
    | _ => throw "inverse supports only Native and JubjubScalar"
    value.validate caps env
  | .cast target (source := source) value => do
    if target.isBytes || source.isBytes then
      throw "byte strings do not support scalar casts"
    if target.isJubjub || source.isJubjub then
      throw "Jubjub values do not support scalar casts"
    target.validate caps
    value.validate caps env
  | .letE (source := source) name value body => do
    value.validate caps env
    body.validate caps ((name, source) :: env)
  | .assertE condition body => do
    condition.validate caps env
    body.validate caps env
  | .disclose _ value => value.validate caps env
  | .eq (ty := operandTy) a b => do
    if operandTy.isBytes then throw "byte string equality is not supported by this source surface"
    if !caps.equality then throw "target lacks equality"
    a.validate caps env
    b.validate caps env
  | .select c a b => do
    if ty.isBytes || ty.isJubjub then
      throw "byte string and Jubjub selection is not supported by this source surface"
    if !caps.select then throw "target lacks conditional selection"
    c.validate caps env
    a.validate caps env
    b.validate caps env
  | .poseidon2 domain a b => do
    if domain >= caps.nativeModulus then throw "noncanonical Poseidon domain"
    if !caps.poseidon2 then throw "target lacks qualified Poseidon support"
    a.validate caps env
    b.validate caps env

def PathKey.validate (caps : Capabilities) (env : TypeEnv) : PathKey → Except String Unit
  | .mk _ value => value.validate caps env

def LedgerValueType.validate (caps : Capabilities) : LedgerValueType → Except String Unit
  | .scalar (.bytes _) => throw "Bytes32 state values are not supported"
  | .scalar .jubjubScalar | .scalar .jubjubPoint =>
    throw "Jubjub values require a qualified ledger schema"
  | .scalar ty => ty.validate caps
  | .map keyTy value => do
    keyTy.validate caps
    value.validate caps
  | .composite environment type => do
    let _ ← checkedNativeRecord environment type
    pure ()

private def resolveTreeState (decls : List StateDecl) (state : String)
    (keys : List PathKey) : Except String LedgerValueType := do
  let some decl := decls.find? (·.name == state) | throw s!"unknown tree state '{state}'"
  let .tree schema := decl.kind | throw s!"state '{state}' is not a recursive map"
  if keys.isEmpty then throw "nested map path must contain at least one key"
  if keys.length > 14 then throw "nested map path exceeds the native insertion depth"
  schema.resolvePath keys

def uniqueNames (names : List String) : Bool := names.eraseDups.length == names.length

/-- Preserve first constraint diagnostic and source span in list order. -/
def validateConstraints (caps : Capabilities) (env : TypeEnv) (span : SourceSpan) :
    List (Expr .bool) → Except Diagnostic Unit
  | [] => .ok ()
  | condition :: rest =>
    match condition.validate caps env with
    | .error message => .error {span, message}
    | .ok _ => validateConstraints caps env span rest

def Circuit.validate (caps : Capabilities) (c : Circuit) : Except Diagnostic Unit := do
  if !uniqueNames (c.inputs.map (·.name)) then
    throw {span := c.span, message := "duplicate circuit input"}
  if !uniqueNames (c.inputs.flatMap Input.nativeIdentifiers) then
    throw {span := c.span, message := "input names collide after native byte expansion"}
  let projections := c.inputs.flatMap Input.publicProjectionIdentifiers
  if !uniqueNames projections || projections.any (fun name =>
      c.inputs.any (fun input => input.name == name)) then
    throw {span := c.span, message := "input names collide with generated Jubjub public projections"}
  if !uniqueNames (c.outputs.map (·.name)) then
    throw {span := c.span, message := "duplicate circuit output"}
  let env := c.inputs.map fun i => (i.name, i.ty)
  for input in c.inputs do
    match input.ty.validate caps with
    | .error message => throw {span := input.span, message}
    | .ok _ => pure ()
  validateConstraints caps env c.span c.constraints
  for output in c.outputs do
    if output.ty.isBytes || output.ty.isJubjub then
      throw {span := output.span, message := "Bytes32 and Jubjub circuit outputs are not supported"}
    match output.ty.validate caps with
    | .error message => throw {span := output.span, message}
    | .ok _ => pure ()
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
  for decl in decls do
    match decl.kind with
    | .cell (.bytes _) | .map _ (.bytes _) =>
      throw {span := decl.span, message := "Bytes32 state values are not supported"}
    | .cell .jubjubScalar | .cell .jubjubPoint
    | .map _ .jubjubScalar | .map _ .jubjubPoint =>
      throw {span := decl.span, message := "Jubjub ledger state requires a qualified point/scalar schema"}
    | .tree schema =>
      match schema.validate caps with
      | .error message => throw {span := decl.span, message}
      | .ok _ => pure ()
    | _ => pure ()
    let types := match decl.kind with
      | .cell ty => [ty]
      | .map keyTy valueTy => [keyTy, valueTy]
      | .tree _ => []
    for ty in types do
      match ty.validate caps with
      | .error message => throw {span := decl.span, message}
      | .ok _ => pure ()
  e.circuit.validate caps
  unless e.effectGuards.isEmpty || e.effectGuards.length == e.effects.length do
    throw {span := e.span, message := "effect guard metadata length mismatch"}
  -- Typing permits private operands. Mandatory disclosure analysis decides
  -- whether their value/control dependence is authorized at a public sink.
  let mut env := e.circuit.inputs.map fun i => (i.name, i.ty)
  for output in e.circuit.outputs do
    if (e.circuit.inputs.find? (·.name == output.name)).isSome then
      throw {span := output.span, message := s!"output '{output.name}' shadows a circuit input"}
    env := env ++ [(output.name, output.ty)]
  for (effect, index) in e.effects.zipIdx do
    let span := e.effectSpans[index]?.getD e.span
    if let some condition := e.effectGuardAt index then
      match condition.validate caps env with
      | .error message => throw {span, message}
      | .ok _ => pure ()
      match effect with
      | .readCell .. | .readMap .. | .readMember .. | .writeCell .. | .writeMap .. |
          .readPath .. | .memberPath .. | .insertPath .. | .writePath .. | .emptyMapPath .. |
          .readCompositePath .. | .writeCompositePath .. => pure ()
      | .require _ => pure ()
      | _ =>
        throw {span := span, message := "native guards are supported only on scalar reads, writes, and require effects"}
    let result : Except String (List (String × Ty)) := do
      match effect with
      | .readCell state destination ty =>
        if !caps.stateCells then throw "target lacks state cells"
        requireState decls state (.cell ty)
        pure [(destination, ty)]
      | .readMap state destination keyTy valueTy key =>
        if !caps.stateMaps then throw "target lacks state maps"
        requireState decls state (.map keyTy valueTy)
        key.validate caps env
        pure [(destination, valueTy)]
      | .readMember state destination keyTy valueTy key =>
        if !caps.stateMaps then throw "target lacks state maps"
        requireState decls state (.map keyTy valueTy)
        key.validate caps env
        pure [(destination, .bool)]
      | .require condition =>
        condition.validate caps env
        pure []
      | .writeCell state ty value =>
        if !caps.stateCells then throw "target lacks state cells"
        requireState decls state (.cell ty)
        value.validate caps env
        pure []
      | .writeMap state keyTy valueTy key value =>
        if !caps.stateMaps then throw "target lacks state maps"
        requireState decls state (.map keyTy valueTy)
        key.validate caps env
        value.validate caps env
        pure []
      | .requireAbsent state keyTy key =>
        if !caps.stateMaps then throw "target lacks state maps"
        match decls.find? (·.name == state) with
        | some {kind := .map found _, ..} =>
          if found != keyTy then throw s!"state key type mismatch for '{state}'"
        | _ => throw s!"unknown map state '{state}'"
        key.validate caps env
        pure []
      | .readPath state destination keys valueTy => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let .scalar found ← resolveTreeState decls state keys
          | throw "nested map read must select a scalar value"
        unless found == valueTy do throw "nested map read value type mismatch"
        valueTy.validate caps
        pure [(destination, valueTy)]
      | .memberPath state destination keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        discard (resolveTreeState decls state keys)
        pure [(destination, .bool)]
      | .insertPath state keys valueTy value
      | .writePath state keys valueTy value => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let .scalar found ← resolveTreeState decls state keys
          | throw "nested scalar write must select a scalar value"
        unless found == valueTy do throw "nested scalar write value type mismatch"
        value.validate caps env
        pure []
      | .readCompositePath state _ keys type destinations => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let .composite compositeEnv foundType ← resolveTreeState decls state keys
          | throw "nested composite read must select a composite value"
        unless foundType == type do throw "nested composite read type mismatch"
        let names ← LedgerValueType.nativeLeafNames compositeEnv type
        unless names.length == destinations.length do
          throw "nested composite read destination count mismatch"
        unless uniqueNames destinations do throw "duplicate nested composite read destination"
        pure (destinations.map fun name => (name, .native))
      | .writeCompositePath state keys type values => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let .composite compositeEnv foundType ← resolveTreeState decls state keys
          | throw "nested composite write must select a composite value"
        unless foundType == type do throw "nested composite write type mismatch"
        let names ← LedgerValueType.nativeLeafNames compositeEnv type
        unless names.length == values.length do throw "nested composite write leaf count mismatch"
        for value in values do value.validate caps env
        pure []
      | .emptyMapPath state keys => do
        if !caps.stateMaps then throw "target lacks state maps"
        for key in keys do key.validate caps env
        let .map _ _ ← resolveTreeState decls state keys
          | throw "emptyMap assignment must select a map value"
        pure []
    match result with
    | .error message => throw {span := e.span, message}
    | .ok bindings =>
      for (name, ty) in bindings do
        if (env.lookup name).isSome then
          throw {span := e.span, message := s!"state read shadows '{name}'"}
        env := env ++ [(name, ty)]

def Contract.validate (caps : Capabilities) (c : Contract) : Except Diagnostic Unit := do
  if !uniqueNames (c.state.map (·.name)) then
    throw {span := c.span, message := "duplicate state declaration"}
  if !uniqueNames (c.entrypoints.map (·.name)) then
    throw {span := c.span, message := "duplicate contract entrypoint"}
  for decl in c.state do
    let types := match decl.kind with
      | .cell ty => [ty]
      | .map keyTy valueTy => [keyTy, valueTy]
      | .tree _ => []
    for ty in types do
      match ty.validate caps with
      | .error message => throw {span := decl.span, message}
      | .ok _ => pure ()
    if let .tree schema := decl.kind then
      match schema.validate caps with
      | .error message => throw {span := decl.span, message}
      | .ok _ => pure ()
  for entry in c.entrypoints do entry.validate caps c.state

end Nightlean
