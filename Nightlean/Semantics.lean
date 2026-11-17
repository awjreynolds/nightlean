import Init.Data.Nat.PowMod
import Nightlean.Disclosure

namespace Nightlean

abbrev Ty.Denote : Ty → Type
  | .native => Nat
  | .bool => Bool
  | .uint _ => Nat
  | .bytes _ => List Nat
  | .jubjubScalar => Nat
  | .jubjubPoint => Nat × Nat

inductive Value where
  | native (value : Nat)
  | bool (value : Bool)
  | uint (maximum value : Nat)
  | bytes (length : Nat) (value : List Nat)
  | jubjubScalar (value : Nat)
  | jubjubPoint (x y : Nat)
  deriving Repr, BEq, DecidableEq

def Value.as : (ty : Ty) → Value → Option ty.Denote
  | .native, .native n => some n
  | .bool, .bool b => some b
  | .uint maximum, .uint found n => if maximum == found then some n else none
  | .bytes length, .bytes found values =>
    if length == found && values.length == length && values.all (· ≤ 255) then some values else none
  | .jubjubScalar, .jubjubScalar scalar => some scalar
  | .jubjubPoint, .jubjubPoint x y => some (x, y)
  | _, _ => none

def Value.pack : (ty : Ty) → ty.Denote → Value
  | .native, n => .native n
  | .bool, b => .bool b
  | .uint maximum, n => .uint maximum n
  | .bytes length, values => .bytes length values
  | .jubjubScalar, scalar => .jubjubScalar scalar
  | .jubjubPoint, (x, y) => .jubjubPoint x y

/-- Recursive semantic form used by the nested-map source effects. -/
inductive LedgerValue where
  | scalar (value : Value)
  | map (entries : List (Value × LedgerValue))
  | composite (type : Types.CompositeType) (leaves : List Nat)
  deriving Repr, BEq

abbrev EvalEnv := List (String × Value)

structure JubjubOracle where
  pointValid : Nat × Nat → Except String Unit :=
    fun _ => .error "qualified Jubjub point-validation oracle is unavailable"
  fromCoordinates : Nat → Nat → Except String (Nat × Nat) :=
    fun _ _ => .error "qualified Jubjub coordinate oracle is unavailable"
  mulGenerator : Nat → Except String (Nat × Nat) :=
    fun _ => .error "qualified Jubjub generator-multiplication oracle is unavailable"
  mul : (Nat × Nat) → Nat → Except String (Nat × Nat) :=
    fun _ _ => .error "qualified Jubjub multiplication oracle is unavailable"
  add : (Nat × Nat) → (Nat × Nat) → Except String (Nat × Nat) :=
    fun _ _ => .error "qualified Jubjub addition oracle is unavailable"
  neg : (Nat × Nat) → Except String (Nat × Nat) :=
    fun _ => .error "qualified Jubjub negation oracle is unavailable"

/-- The crypto oracles have fail-closed defaults. A backend must supply pinned
Jubjub operations before semantic evaluation can execute curve expressions. -/
structure EvalContext where
  modulus : Nat
  poseidon2 : Nat → Nat → Nat → Except String Nat
  /-- Qualified host implementation of the pinned Bytes32 persistent hash.
  The default rejects, so evaluation never substitutes a placeholder hash. -/
  persistentHash32 : List Nat → Except String (List Nat) :=
    fun _ => .error "qualified Bytes32 persistent-hash oracle is unavailable"
  jubjub : JubjubOracle := {}

private def sameValue : (ty : Ty) → ty.Denote → ty.Denote → Bool
  | .native, a, b => a == b
  | .bool, a, b => a == b
  | .uint _, a, b => a == b
  | .bytes _, a, b => a == b
  | .jubjubScalar, a, b => a == b
  | .jubjubPoint, a, b => a == b

private def canonical (ctx : EvalContext) (ty : Ty) (v : ty.Denote) : Bool :=
  match ty with
  | .native => v < ctx.modulus
  | .bool => true
  | .uint maximum => maximum ≤ ScalarPolicy.maxUint && v ≤ maximum && v < ctx.modulus
  | .bytes length => v.length == length && v.all (· ≤ 255)
  | .jubjubScalar => v < Jubjub.scalarOrder
  | .jubjubPoint => v.1 < ctx.modulus && v.2 < ctx.modulus &&
      (ctx.jubjub.pointValid v).isOk

/-- Public reduction equation for input-admission and preservation proofs. -/
theorem canonical_eq (ctx : EvalContext) (ty : Ty) (value : ty.Denote) :
    canonical ctx ty value = match ty with
      | .native => value < ctx.modulus
      | .bool => true
      | .uint maximum => maximum ≤ ScalarPolicy.maxUint && value ≤ maximum && value < ctx.modulus
      | .bytes length => value.length == length && value.all (· ≤ 255)
      | .jubjubScalar => value < Jubjub.scalarOrder
      | .jubjubPoint => value.1 < ctx.modulus && value.2 < ctx.modulus &&
          (ctx.jubjub.pointValid value).isOk := rfl

private def scalarNumber : (ty : Ty) → ty.Denote → Except String Nat
  | .native, n | .uint _, n => pure n
  | .bool, b => pure (if b then 1 else 0)
  | .bytes _, _ => .error "byte strings do not support scalar conversion"
  | .jubjubScalar, _ => .error "Jubjub scalars do not support scalar conversion"
  | .jubjubPoint, _ => .error "Jubjub points do not support scalar conversion"

private def scalarCast (ctx : EvalContext) (target : Ty) (number : Nat) : Except String target.Denote :=
  match target with
  | .native => if number < ctx.modulus then pure number else .error "noncanonical scalar conversion"
  | .bool => pure (number != 0)
  | .uint maximum =>
    if maximum ≤ ScalarPolicy.maxUint && number ≤ maximum && number < ctx.modulus then pure number
    else .error "scalar conversion exceeds unsigned bound"
  | .bytes _ => .error "byte strings do not support scalar conversion"
  | .jubjubScalar | .jubjubPoint => .error "Jubjub values do not support scalar conversion"

private def checkedJubjubPoint (ctx : EvalContext) (point : Nat × Nat) :
    Except String (Nat × Nat) := do
  if point.1 >= ctx.modulus || point.2 >= ctx.modulus then
    throw "noncanonical Jubjub coordinate"
  ctx.jubjub.pointValid point
  pure point

/-- Pinned native Bytes field packing: little-endian bytes within each
FR_BYTES_STORED-sized chunk, with the chunk sequence reversed. For Bytes32 the
two chunks are byte 31 first, followed by bytes 0 through 30. -/
private def bytesFieldChunk (length chunkIndex : Nat) (values : List Nat) : Nat := Id.run do
  let chunks := (length + 30) / 31
  let rawIndex := chunks - 1 - chunkIndex
  let start := rawIndex * 31
  let size := min 31 (length - start)
  let part := values.drop start |>.take size
  let mut result := 0
  for (value, index) in part.zipIdx do
    result := result + value * 256 ^ index
  return result

private def nativeFieldBytesLE (value : Nat) : List Nat :=
  go value 32
where
  go (remaining : Nat) : Nat → List Nat
    | 0 => []
    | count + 1 => remaining % 256 :: go (remaining / 256) count

private def evaluatePersistentHash (ctx : EvalContext) (preimage : List Nat) :
    Except String (List Nat) := do
  let result ← ctx.persistentHash32 preimage
  if result.length != 32 || !result.all (· ≤ 255) then
    throw "persistent-hash oracle returned a malformed Bytes32 digest"
  pure result

private def checkedPrimeFieldInverse (value modulus : Nat) : Except String Nat := do
  if modulus ≤ 2 then throw "invalid prime-field modulus for inverse"
  if value == 0 then throw "inverse of zero is undefined"
  if value ≥ modulus then throw "inverse operand is outside its prime field"
  let inverse := Nat.powMod value (modulus - 2) modulus
  if value * inverse % modulus != 1 then
    throw "prime-field inverse failed its multiplication postcondition"
  pure inverse

/-- Evaluation is total and returns errors for absent/mistyped witnesses or
noncanonical field data, rather than silently inventing witness values. -/
def Expr.eval (ctx : EvalContext) (env : EvalEnv) : Expr ty → Except String ty.Denote
  | .native n => if n < ctx.modulus then pure n else .error "noncanonical native constant"
  | .bool b => .ok b
  | .uint maximum n =>
    if canonical ctx (.uint maximum) n then pure n else .error "noncanonical unsigned constant"
  | .bytesField (length := length) value index => do
    let values ← value.eval ctx env
    let result := bytesFieldChunk length index values
    if result < ctx.modulus then pure result else .error "noncanonical packed byte field"
  | .bytes32Literal values =>
    if values.length == 32 && values.all (· ≤ 255) then pure values
    else .error "Bytes32 literal must contain exactly 32 byte values"
  | .jubjubScalarFromNative value => do
    pure ((← value.eval ctx env) % Jubjub.scalarOrder)
  | .jubjubScalarToNative value => do
    let scalar ← value.eval ctx env
    if scalar < ctx.modulus then pure scalar else .error "Jubjub scalar does not fit Native"
  | .jubjubMulGenerator scalar => do
    checkedJubjubPoint ctx (← ctx.jubjub.mulGenerator (← scalar.eval ctx env))
  | .jubjubMul point scalar => do
    checkedJubjubPoint ctx (← ctx.jubjub.mul (← point.eval ctx env) (← scalar.eval ctx env))
  | .jubjubAdd left right => do
    checkedJubjubPoint ctx (← ctx.jubjub.add (← left.eval ctx env) (← right.eval ctx env))
  | .jubjubNeg point => do
    checkedJubjubPoint ctx (← ctx.jubjub.neg (← point.eval ctx env))
  | .jubjubCoordinate point index => do
    let (x, y) ← point.eval ctx env
    match index with
    | 0 => pure x
    | 1 => pure y
    | _ => throw "Jubjub coordinate index must be 0 or 1"
  | .jubjubFromCoordinates x y => do
    checkedJubjubPoint ctx (← ctx.jubjub.fromCoordinates (← x.eval ctx env) (← y.eval ctx env))
  | .bytesAt value index => do
    let values ← value.eval ctx env
    match values[index]? with
    | some byte => if byte ≤ 255 then pure byte else .error "noncanonical Bytes32 byte"
    | none => .error "Bytes32 byte index is out of range"
  | .persistentHash32 value => do
    let input ← value.eval ctx env
    evaluatePersistentHash ctx input
  | .persistentHashVector32 values => do
    if values.length < 1 || values.length > 32 then
      throw "persistent hash vector must contain 1 to 32 Bytes32 values"
    let mut preimage := []
    for value in values do preimage := preimage ++ (← value.eval ctx env)
    evaluatePersistentHash ctx preimage
  | .persistentHashNative value => do
    let field ← value.eval ctx env
    evaluatePersistentHash ctx (nativeFieldBytesLE field)
  | .persistentHashNativeVector values => do
    if values.isEmpty || values.length > 32 then
      throw "Native persistent-hash vector must contain 1 to 32 fields"
    let mut preimage := []
    for value in values do
      preimage := preimage ++ nativeFieldBytesLE (← value.eval ctx env)
    evaluatePersistentHash ctx preimage
  | .inv (ty := .native) value => do
    checkedPrimeFieldInverse (← value.eval ctx env) ctx.modulus
  | .inv (ty := .jubjubScalar) value => do
    checkedPrimeFieldInverse (← value.eval ctx env) Jubjub.scalarOrder
  | .inv _ => .error "inverse supports only Native and JubjubScalar"
  | .ref name => do
    let some raw := env.lookup name | throw s!"missing value '{name}'"
    let some value := raw.as ty | throw s!"value type mismatch for '{name}'"
    if !canonical ctx ty value then throw s!"noncanonical value '{name}'"
    pure value
  | .add a b => do
    if ctx.modulus == 0 then throw "invalid zero field modulus"
    pure (((← a.eval ctx env) + (← b.eval ctx env)) % ctx.modulus)
  | .mul a b => do
    if ctx.modulus == 0 then throw "invalid zero field modulus"
    pure (((← a.eval ctx env) * (← b.eval ctx env)) % ctx.modulus)
  | .sub a b => do
    if ctx.modulus == 0 then throw "invalid zero field modulus"
    pure ((ctx.modulus + (← a.eval ctx env) - (← b.eval ctx env)) % ctx.modulus)
  | .uadd (m := m) (n := n) a b => do
    let result := (← a.eval ctx env) + (← b.eval ctx env)
    scalarCast ctx (.uint (m + n)) result
  | .umul (m := m) (n := n) a b => do
    let result := (← a.eval ctx env) * (← b.eval ctx env)
    scalarCast ctx (.uint (m * n)) result
  | .usub (m := m) a b => do
    let a ← a.eval ctx env
    let b ← b.eval ctx env
    if a < b then throw "unsigned subtraction underflow"
    scalarCast ctx (.uint m) (a - b)
  | .cast (source := source) target value => do
    if target.isBytes || source.isBytes || target.isJubjub || source.isJubjub then
      throw "byte strings and Jubjub values do not support scalar conversion"
    scalarCast ctx target (← scalarNumber source (← value.eval ctx env))
  | .letE (source := source) name value body => do
    let value ← value.eval ctx env
    body.eval ctx ((name, Value.pack source value) :: env)
  | .assertE condition body => do
    unless (← condition.eval ctx env) do throw "helper assertion failed"
    body.eval ctx env
  | .disclose _ value => value.eval ctx env
  | .eq (ty := ty) a b => do
    pure (sameValue ty (← a.eval ctx env) (← b.eval ctx env))
  | .select c a b => do
    let condition ← c.eval ctx env
    let yes ← a.eval ctx env
    let no ← b.eval ctx env
    pure (if condition then yes else no)
  | .poseidon2 domain a b => do
    if domain >= ctx.modulus then throw "noncanonical Poseidon domain"
    let value ← ctx.poseidon2 domain (← a.eval ctx env) (← b.eval ctx env)
    if value >= ctx.modulus then throw "hash oracle returned noncanonical value"
    pure value

/-- Check constraints in source order, preserving the first evaluation error. -/
def runConstraints (ctx : EvalContext) (env : EvalEnv) : List (Expr .bool) → Except String Unit
  | [] => .ok ()
  | condition :: rest =>
    match condition.eval ctx env with
    | .error message => .error message
    | .ok false => .error "circuit constraint failed"
    | .ok true => runConstraints ctx env rest

theorem disclose_evaluation (ctx : EvalContext) (env : EvalEnv) (span : SourceSpan) (value : Expr ty) :
    (Expr.disclose span value).eval ctx env = value.eval ctx env := by
  simp [Expr.eval]

private def evaluationCapabilities (ctx : EvalContext) : Capabilities :=
  {nativeModulus := ctx.modulus, poseidon2 := true, persistentHash32 := true,
    persistentHashVector32 := true, persistentHashNative := true, jubjub := true}

def Circuit.run (ctx : EvalContext) (c : Circuit) (env : EvalEnv) : Except String EvalEnv := do
  match c.validate (evaluationCapabilities ctx) with
  | .error diagnostic => throw diagnostic.message
  | .ok _ => pure ()
  if !uniqueNames (env.map Prod.fst) then throw "duplicate input value"
  for (name, _) in env do
    if !(c.inputs.any (·.name == name)) then throw s!"undeclared input value '{name}'"
  for input in c.inputs do
    let some raw := env.lookup input.name | throw s!"missing input '{input.name}'"
    let some value := raw.as input.ty | throw s!"input type mismatch for '{input.name}'"
    if !canonical ctx input.ty value then throw s!"noncanonical input '{input.name}'"
  runConstraints ctx env c.constraints
  c.outputs.mapM fun output => do
    pure (output.name, Value.pack output.ty (← output.value.eval ctx env))

/-- Pure transaction state. A failed transition returns no successor state. -/
structure LedgerState where
  cells : List (String × Value) := []
  maps : List (String × List (Value × Value)) := []
  trees : List (String × LedgerValue) := []
  deriving Repr, BEq

private def updateAssoc [BEq α] (key : α) (value : β) (entries : List (α × β)) : List (α × β) :=
  (key, value) :: entries.filter (fun item => !(item.1 == key))

private def evaluatePath (ctx : EvalContext) (env : EvalEnv) (keys : List PathKey) :
    Except String (List Value) := keys.mapM fun key => match key with
  | .mk ty expression => do
    let value ← expression.eval ctx env
    if !canonical ctx ty value then throw "noncanonical nested map key"
    pure (Value.pack ty value)

private def treeLookup (root : LedgerValue) : List Value → Option LedgerValue
  | [] => some root
  | key :: rest => match root with
    | .scalar _ => none
    | .composite .. => none
    | .map entries => (entries.lookup key).bind fun value => treeLookup value rest

private def treeMember (root : LedgerValue) (keys : List Value) : Except String Bool := do
  if keys.isEmpty then throw "nested membership path must contain at least one key"
  let parent ← match treeLookup root (keys.take (keys.length - 1)) with
    | some parent => pure parent
    | none => throw "nested membership parent is missing"
  let .map entries := parent | throw "nested membership parent is not a map"
  let some key := keys.getLast? | throw "nested membership path must contain at least one key"
  pure (entries.lookup key).isSome

private def treeSet (root : LedgerValue) (keys : List Value) (value : LedgerValue) :
    Option LedgerValue := do
  match keys with
  | [] => pure value
  | key :: rest =>
    match root with
    | .scalar _ => none
    | .composite .. => none
    | .map entries =>
      if rest.isEmpty then
        pure (.map (updateAssoc key value entries))
      else do
        let child ← entries.lookup key
        let next ← treeSet child rest value
        pure (.map (updateAssoc key next entries))

/-- Execute ordered effects against a private tentative state. Returning an error
never exposes that tentative state, expressing atomic failure in the reference model. -/
def runEffects (ctx : EvalContext) (effects : List Effect) (env : EvalEnv)
    (state : LedgerState) : Except String LedgerState := do
  let mut env := env
  let mut next := state
  for effect in effects do
    match effect with
    | .readCell name destination ty =>
      let some raw := next.cells.lookup name | throw s!"missing state cell '{name}'"
      let some value := raw.as ty | throw s!"state cell type mismatch '{name}'"
      if !canonical ctx ty value then throw s!"noncanonical state cell '{name}'"
      env := (destination, Value.pack ty value) :: env
    | .readMap name destination keyTy valueTy key =>
      let key := Value.pack keyTy (← key.eval ctx env)
      let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
      let some raw := entries.lookup key | throw s!"missing map key in '{name}'"
      let some value := raw.as valueTy | throw s!"state map value type mismatch '{name}'"
      if !canonical ctx valueTy value then throw s!"noncanonical state map value '{name}'"
      env := (destination, Value.pack valueTy value) :: env
    | .readMember name destination keyTy valueTy key =>
      let key := Value.pack keyTy (← key.eval ctx env)
      let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
      for (oldKey, oldValue) in entries do
        let some keyValue := oldKey.as keyTy | throw s!"state map key type mismatch '{name}'"
        let some value := oldValue.as valueTy | throw s!"state map value type mismatch '{name}'"
        if !canonical ctx keyTy keyValue || !canonical ctx valueTy value then
          throw s!"noncanonical state map entry '{name}'"
      env := (destination, Value.bool (entries.lookup key).isSome) :: env
    | .require condition =>
      if !(← condition.eval ctx env) then throw "state transition guard failed"
    | .writeCell name ty value =>
      let some existing := next.cells.lookup name | throw s!"missing state cell '{name}'"
      if (existing.as ty).isNone then throw s!"state cell type mismatch '{name}'"
      next := {next with cells := updateAssoc name (Value.pack ty (← value.eval ctx env)) next.cells}
    | .writeMap name keyTy valueTy key value =>
      let key := Value.pack keyTy (← key.eval ctx env)
      let value := Value.pack valueTy (← value.eval ctx env)
      let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
      for (oldKey, oldValue) in entries do
        if (oldKey.as keyTy).isNone || (oldValue.as valueTy).isNone then
          throw s!"state map type mismatch '{name}'"
      next := {next with maps := updateAssoc name (updateAssoc key value entries) next.maps}
    | .requireAbsent name keyTy key =>
      let key := Value.pack keyTy (← key.eval ctx env)
      let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
      if (entries.lookup key).isSome then throw "state map key already present"
    | .readPath name destination keys ty => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      let some (.scalar raw) := treeLookup root evaluated
        | throw s!"missing or non-scalar nested map value '{name}'"
      let some value := raw.as ty | throw s!"nested map value type mismatch '{name}'"
      if !canonical ctx ty value then throw s!"noncanonical nested map value '{name}'"
      env := (destination, Value.pack ty value) :: env
    | .readCompositePath name _ keys type destinations => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      let some (.composite found leaves) := treeLookup root evaluated
        | throw s!"missing or non-composite nested map value '{name}'"
      unless found == type && leaves.length == destinations.length do
        throw s!"nested composite state type mismatch '{name}'"
      unless leaves.all (· < ctx.modulus) do throw s!"noncanonical nested composite value '{name}'"
      env := env ++ (destinations.zip leaves).map fun (destination, value) =>
        (destination, .native value)
    | .memberPath name destination keys => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      env := (destination, .bool (← treeMember root evaluated)) :: env
    | .insertPath name keys ty value | .writePath name keys ty value => do
      let evaluated ← evaluatePath ctx env keys
      let payload := LedgerValue.scalar (Value.pack ty (← value.eval ctx env))
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      let some updated := treeSet root evaluated payload
        | throw s!"nested map parent is missing or not a map '{name}'"
      next := {next with trees := updateAssoc name updated next.trees}
    | .writeCompositePath name keys type values => do
      let evaluated ← evaluatePath ctx env keys
      let leaves ← values.mapM (fun value => value.eval ctx env)
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      let some updated := treeSet root evaluated (.composite type leaves)
        | throw s!"nested map parent is missing or not a map '{name}'"
      next := {next with trees := updateAssoc name updated next.trees}
    | .emptyMapPath name keys => do
      let evaluated ← evaluatePath ctx env keys
      let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
      let some updated := treeSet root evaluated (.map [])
        | throw s!"nested map parent is missing or not a map '{name}'"
      next := {next with trees := updateAssoc name updated next.trees}
  pure next

/-- Execute source effects with optional scalar read/write and require guards.
Inactive reads bind their canonical zero without touching state or keys. -/
def runEffectsWithGuards (ctx : EvalContext) (effects : List Effect)
    (guards : List (Option (Expr .bool))) (env : EvalEnv)
    (state : LedgerState) : Except String LedgerState := do
  unless guards.isEmpty || guards.length == effects.length do
    throw "effect guard metadata length mismatch"
  if guards.isEmpty then
    runEffects ctx effects env state
  else do
    let mut env := env
    let mut next := state
    for (effect, index) in effects.zipIdx do
      let guard := guards[index]?.getD none
      if guard.isSome then
        match effect with
        | .readCell .. | .readMap .. | .readMember .. | .writeCell .. | .writeMap .. | .require .. |
            .readPath .. | .readCompositePath .. | .memberPath .. | .insertPath .. |
            .writePath .. | .writeCompositePath .. | .emptyMapPath .. => pure ()
        | _ => throw "native guards are supported only on scalar reads, writes, and require effects"
      let active ← match guard with
        | some condition => condition.eval ctx env
        | _ => pure true
      if active then
        match effect with
        | .readCell name destination ty =>
          let some raw := next.cells.lookup name | throw s!"missing state cell '{name}'"
          let some value := raw.as ty | throw s!"state cell type mismatch '{name}'"
          if !canonical ctx ty value then throw s!"noncanonical state cell '{name}'"
          env := (destination, Value.pack ty value) :: env
        | .readMap name destination keyTy valueTy key =>
          let key := Value.pack keyTy (← key.eval ctx env)
          let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
          let some raw := entries.lookup key | throw s!"missing map key in '{name}'"
          let some value := raw.as valueTy | throw s!"state map value type mismatch '{name}'"
          if !canonical ctx valueTy value then throw s!"noncanonical state map value '{name}'"
          env := (destination, Value.pack valueTy value) :: env
        | .readMember name destination keyTy valueTy key =>
          let key := Value.pack keyTy (← key.eval ctx env)
          let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
          for (oldKey, oldValue) in entries do
            let some keyValue := oldKey.as keyTy | throw s!"state map key type mismatch '{name}'"
            let some value := oldValue.as valueTy | throw s!"state map value type mismatch '{name}'"
            if !canonical ctx keyTy keyValue || !canonical ctx valueTy value then
              throw s!"noncanonical state map entry '{name}'"
          env := (destination, Value.bool (entries.lookup key).isSome) :: env
        | .require condition =>
          if !(← condition.eval ctx env) then throw "state transition guard failed"
        | .writeCell name ty value =>
          let some existing := next.cells.lookup name | throw s!"missing state cell '{name}'"
          if (existing.as ty).isNone then throw s!"state cell type mismatch '{name}'"
          next := {next with cells := updateAssoc name (Value.pack ty (← value.eval ctx env)) next.cells}
        | .writeMap name keyTy valueTy key value =>
          let key := Value.pack keyTy (← key.eval ctx env)
          let value := Value.pack valueTy (← value.eval ctx env)
          let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
          for (oldKey, oldValue) in entries do
            if (oldKey.as keyTy).isNone || (oldValue.as valueTy).isNone then
              throw s!"state map type mismatch '{name}'"
          next := {next with maps := updateAssoc name (updateAssoc key value entries) next.maps}
        | .requireAbsent name keyTy key =>
          let key := Value.pack keyTy (← key.eval ctx env)
          let some entries := next.maps.lookup name | throw s!"missing state map '{name}'"
          if (entries.lookup key).isSome then throw "state map key already present"
        | .readPath name destination keys ty => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          let some (.scalar raw) := treeLookup root evaluated
            | throw s!"missing or non-scalar nested map value '{name}'"
          let some value := raw.as ty | throw s!"nested map value type mismatch '{name}'"
          if !canonical ctx ty value then throw s!"noncanonical nested map value '{name}'"
          env := (destination, Value.pack ty value) :: env
        | .readCompositePath name _ keys type destinations => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          let some (.composite found leaves) := treeLookup root evaluated
            | throw s!"missing or non-composite nested map value '{name}'"
          unless found == type && leaves.length == destinations.length do
            throw s!"nested composite state type mismatch '{name}'"
          unless leaves.all (· < ctx.modulus) do throw s!"noncanonical nested composite value '{name}'"
          env := env ++ (destinations.zip leaves).map fun (destination, value) =>
            (destination, .native value)
        | .memberPath name destination keys => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          env := (destination, .bool (← treeMember root evaluated)) :: env
        | .insertPath name keys ty value | .writePath name keys ty value => do
          let evaluated ← evaluatePath ctx env keys
          let payload := LedgerValue.scalar (Value.pack ty (← value.eval ctx env))
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          let some updated := treeSet root evaluated payload
            | throw s!"nested map parent is missing or not a map '{name}'"
          next := {next with trees := updateAssoc name updated next.trees}
        | .writeCompositePath name keys type values => do
          let evaluated ← evaluatePath ctx env keys
          let leaves ← values.mapM (fun value => value.eval ctx env)
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          let some updated := treeSet root evaluated (.composite type leaves)
            | throw s!"nested map parent is missing or not a map '{name}'"
          next := {next with trees := updateAssoc name updated next.trees}
        | .emptyMapPath name keys => do
          let evaluated ← evaluatePath ctx env keys
          let some root := next.trees.lookup name | throw s!"missing recursive state map '{name}'"
          let some updated := treeSet root evaluated (.map [])
            | throw s!"nested map parent is missing or not a map '{name}'"
          next := {next with trees := updateAssoc name updated next.trees}
      else
        match effect with
        | .readCell _ destination ty =>
          let zero : ty.Denote := match ty with
            | .native => 0
            | .bool => false
            | .uint _ => 0
            | .bytes length => List.replicate length 0
            | .jubjubScalar => 0
            | .jubjubPoint => (0, 1)
          env := (destination, Value.pack ty zero) :: env
        | .readMap _ destination _ ty _ =>
          let zero : ty.Denote := match ty with
            | .native => 0
            | .bool => false
            | .uint _ => 0
            | .bytes length => List.replicate length 0
            | .jubjubScalar => 0
            | .jubjubPoint => (0, 1)
          env := (destination, Value.pack ty zero) :: env
        | .readMember _ destination .. =>
          env := (destination, .bool false) :: env
        | .writeCell .. | .writeMap .. | .require .. | .insertPath .. | .writePath .. |
            .writeCompositePath .. | .emptyMapPath .. => pure ()
        | .readPath _ destination _ ty =>
          let zero : ty.Denote := match ty with
            | .native => 0
            | .bool => false
            | .uint _ => 0
            | .bytes length => List.replicate length 0
            | .jubjubScalar => 0
            | .jubjubPoint => (0, 1)
          env := (destination, Value.pack ty zero) :: env
        | .readCompositePath _ _ _ _ destinations =>
          env := env ++ destinations.map fun destination => (destination, .native 0)
        | .memberPath _ destination _ => env := (destination, .bool false) :: env
        | _ => throw "native guards are supported only on scalar reads, writes, and require effects"
    pure next

/-- This is a specification evaluator, not a substitute for ledger proof checks. -/
def Entrypoint.run (ctx : EvalContext) (entry : Entrypoint) (env : EvalEnv)
    (state : LedgerState) : Except String (EvalEnv × LedgerState) := do
  match Disclosure.entrypoint entry with
  | .error diagnostic => throw diagnostic.message
  | .ok _ => pure ()
  let outputs ← entry.circuit.run ctx env
  let next ← runEffectsWithGuards ctx entry.effects entry.effectGuards (outputs ++ env) state
  pure (outputs, next)

/-- A small optimization whose correctness does not depend on the backend or hash. -/
def pruneTrue : List (Expr .bool) → List (Expr .bool)
  | [] => []
  | .bool true :: rest => pruneTrue rest
  | condition :: rest => condition :: pruneTrue rest

def ConstraintsHold (ctx : EvalContext) (env : EvalEnv) : List (Expr .bool) → Prop
  | [] => True
  | condition :: rest => condition.eval ctx env = .ok true ∧ ConstraintsHold ctx env rest

theorem pruneTrue_preserves (ctx : EvalContext) (env : EvalEnv) (conditions : List (Expr .bool)) :
    ConstraintsHold ctx env (pruneTrue conditions) ↔ ConstraintsHold ctx env conditions := by
  induction conditions with
  | nil => rfl
  | cons condition rest ih =>
    cases condition with
    | bool b => cases b <;> simp [pruneTrue, ConstraintsHold, Expr.eval, ih]
    | ref name => simp [pruneTrue, ConstraintsHold, ih]
    | eq a b => simp [pruneTrue, ConstraintsHold, ih]
    | select condition a b => simp [pruneTrue, ConstraintsHold, ih]
    | cast target value => simp [pruneTrue, ConstraintsHold, ih]
    | letE name value body => simp [pruneTrue, ConstraintsHold, ih]
    | assertE condition body => simp [pruneTrue, ConstraintsHold, ih]
    | disclose span value => simp [pruneTrue, ConstraintsHold, ih]
    | inv value => simp [pruneTrue, ConstraintsHold, ih]

theorem unsigned_addition_no_wrap (a b m n : Nat) (ha : a ≤ m) (hb : b ≤ n)
    (hbound : m + n ≤ ScalarPolicy.maxUint) : (a + b) % Field.modulus = a + b :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
    (Nat.le_trans (ScalarPolicy.addition_range a b m n ha hb) hbound)
    ScalarPolicy.maxUint_lt_native)

theorem unsigned_multiplication_no_wrap (a b m n : Nat) (ha : a ≤ m) (hb : b ≤ n)
    (hbound : m * n ≤ ScalarPolicy.maxUint) : (a * b) % Field.modulus = a * b :=
  Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt
    (Nat.le_trans (ScalarPolicy.multiplication_range a b m n ha hb) hbound)
    ScalarPolicy.maxUint_lt_native)

/-- An underflowed field subtraction lies above every supported unsigned bound. -/
theorem unsigned_underflow_outside_range (a b : Nat) (_hab : a < b)
    (hb : b ≤ ScalarPolicy.maxUint) : ScalarPolicy.maxUint < Field.modulus + a - b := by
  have hseparation : 2 * ScalarPolicy.maxUint < Field.modulus := by decide
  omega

theorem unsigned_underflow_modulo_rejected (a b : Nat) (hab : a < b)
    (hb : b ≤ ScalarPolicy.maxUint) :
    ScalarPolicy.maxUint < (Field.modulus + a - b) % Field.modulus := by
  have hfield := ScalarPolicy.maxUint_lt_native
  have hbelow : Field.modulus + a - b < Field.modulus := by omega
  rw [Nat.mod_eq_of_lt hbelow]
  exact unsigned_underflow_outside_range a b hab hb

end Nightlean
