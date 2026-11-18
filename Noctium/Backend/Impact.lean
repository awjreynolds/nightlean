import Noctium.IR
import Noctium.Field
import Noctium.Semantics
import Noctium.Disclosure
import Noctium.Types.ValueSchema
import Lean

namespace Noctium.Backend.Impact

private def expressionCapabilities : Capabilities :=
  {poseidon2 := true, persistentHash32 := true, persistentHashVector32 := true,
    persistentHashNative := true, bytes32Conversions := true, sha512 := true, keccak256 := true, typedBoolean := true, hashToCurve := true, foreignValues := true, jubjub := true}

private def ledgerCapabilities : Capabilities :=
  {poseidon2 := true, persistentHash32 := true, persistentHashVector32 := true,
    persistentHashNative := true, bytes32Conversions := true, sha512 := true, keccak256 := true, typedBoolean := true, hashToCurve := true, foreignValues := true, jubjub := true,
    stateCells := true, stateMaps := true}

/-- Symbols in the ledger public-input sequence are source expressions, not
free transcript values. Each symbol must be computed or publicly read by ZKIR. -/
abbrev Scalar := Expr .native

inductive Aligned where
  | field (value : Scalar)
  | bit (value : Bool)
  | bitExpr (value : Expr .bool)
  | bytes32 (value : Expr (.bytes 32))
  | nativeFields (values : List Scalar)
  | counter (value : Expr (.uint (2 ^ 64 - 1)))
  deriving Repr

inductive Op where
  | dup
  | index (slot : Nat) (pushPath : Bool := false)
  | mapIndex (slot : Nat) (key : Aligned)
  | indexPath (slot : Nat) (pushPath : Bool) (keys : List Aligned)
  | push (value : Aligned) (storage : Bool := false)
  | newMap
  | popeq (value : Aligned)
  | pushFields (schema : Lean.Json) (values : List Scalar) (storage : Bool := false)
  | popeqFields (schema : Lean.Json) (values : List Scalar)
  | member
  | insert (levels : Nat)
  | addImmediate (amount : Nat)
  | subImmediate (amount : Nat)
  | listLength (slot : Nat) (keys : List Aligned) (value : Expr (.uint (2 ^ 64 - 1)))
  | listHead (slot : Nat) (keys : List Aligned) (schema : Lean.Json) (values : List Scalar)
  | listPushFront (slot : Nat) (keys : List Aligned) (schema : Lean.Json) (values : List Scalar)
  | listPopFront (slot : Nat) (keys : List Aligned)
  | listReset (slot : Nat) (keys : List Aligned)
  | mapRemove (slot : Nat) (keys : List Aligned)

/-- Field-representation vectors match ledger-9 onchain-vm/src/ops.rs and
transient-crypto/src/fab.rs. Map-key alignment follows the declared key type. -/
def Aligned.fields : Aligned → List Scalar
  | .field value => [.native 1, .native (Field.modulus - 2), value]
  | .bit value => [.native 1, .native 1, .native (if value then 1 else 0)]
  | .bitExpr value => [.native 1, .native 1,
      .select value (.native 1) (.native 0)]
  | .bytes32 value => [.native 1, .native 32,
      .bytesField value 0, .bytesField value 1]
  | .nativeFields values => [.native values.length] ++
      List.replicate values.length (.native (Field.modulus - 2)) ++ values
  | .counter value => [.native 1, .native 8, .cast .native value]

private def indexPathFields (slot : Nat) (pushPath : Bool) (keys : List Aligned) : List Scalar :=
  [.native ((if pushPath then 0x70 else 0x50) + keys.length)] ++
    (Aligned.field (.native slot)).fields ++ keys.flatMap Aligned.fields

private def listIndexFields (index : Nat) : List Scalar :=
  [.native 0x50, .native 1, .native 1, .native index]

private def listU8CellPushFields (index : Nat) : List Scalar :=
  [.native 0x10, .native 1, .native 1, .native 1, .native index]

private def listNodePushFields (values : List Scalar) : List Scalar :=
  [.native 0x11, .native 51, .native 1, .native values.length] ++
    List.replicate values.length (.native (Field.modulus - 2)) ++ values ++
    [.native 0, .native 0]

private def emptyListPushFields : List Scalar :=
  [.native 0x11, .native 51, .native 0, .native 0,
    .native 1, .native 1, .native 8, .native 0]

def Op.fields : Op → List Scalar
  | .dup => [.native 0x30]
  | .index slot pushPath => [.native (if pushPath then 0x70 else 0x50)] ++
      (Aligned.field (.native slot)).fields
  | .mapIndex slot key => [.native 0x51] ++
      (Aligned.field (.native slot)).fields ++ key.fields
  | .indexPath slot pushPath keys => indexPathFields slot pushPath keys
  | .push value storage => [.native (if storage then 0x11 else 0x10), .native 1] ++ value.fields
  | .newMap => [.native 0x05]
  | .popeq value => [.native 0x0c] ++ value.fields
  | .pushFields _ values storage =>
      [.native (if storage then 0x11 else 0x10), .native 1] ++
        (Aligned.nativeFields values).fields
  | .popeqFields _ values => [.native 0x0c] ++ (Aligned.nativeFields values).fields
  | .member => [.native 0x18]
  | .insert levels => [.native (0x90 + levels)]
  | .addImmediate amount => [.native 0x0e, .native amount]
  | .subImmediate amount => [.native 0x0f, .native amount]
  | .listLength slot keys value =>
      [.native 0x30] ++ indexPathFields slot false keys ++
      listIndexFields 2 ++ [.native 0x0c] ++ (Aligned.counter value).fields
  | .listHead slot keys _schema values =>
      [.native 0x30] ++ indexPathFields slot false keys ++ listIndexFields 0 ++
      [.native 0x0c] ++ (Aligned.nativeFields values).fields
  | .listPushFront slot keys _ values =>
      indexPathFields slot true keys ++ [.native 0x30] ++ listIndexFields 2 ++
      [.native 0x0e, .native 1] ++ listNodePushFields values ++
      [.native 0x40, .native 0x10, .native 1, .native 1, .native 1, .native 2] ++
      [.native 0x40, .native 0x91, .native 0x40, .native 0x10, .native 1,
        .native 1, .native 1, .native 1, .native 0x40, .native (0x90 + keys.length + 2)]
  | .listPopFront slot keys =>
      indexPathFields slot true keys ++ [.native 0x30] ++ listIndexFields 2 ++
      [.native 0x0f, .native 1, .native 0x0b] ++ listIndexFields 1 ++
      [.native (0x90 + keys.length + 1)]
  | .listReset slot keys =>
      match keys with
      | [] => [.native 0x10, .native 1] ++ (Aligned.field (.native slot)).fields ++
          emptyListPushFields ++ [.native 0x91]
      | _ => match keys.getLast? with
        | none => []
        | some finalKey =>
          let parents := keys.take (keys.length - 1)
          indexPathFields slot true parents ++ [.native 0x10, .native 1] ++
            finalKey.fields ++ emptyListPushFields ++ [.native (0x90 + keys.length + 1)]
  | .mapRemove slot keys =>
      match keys.getLast? with
      | none => []
      | some finalKey =>
        let parents := keys.take (keys.length - 1)
        indexPathFields slot true parents ++ [.native 0x10, .native 1] ++
          finalKey.fields ++ [.native 0x19, .native (0x90 + keys.length)]

/-- Native transcript groups correspond one-to-one with VM operations. List
macros remain one typed source effect, but their field vectors split at each
elementary opcode so activity schedules match the ledger VM. -/
def Op.fieldGroups : Op → List (List Scalar)
  | .listLength slot keys value =>
      [[.native 0x30], indexPathFields slot false keys, listIndexFields 2,
        [.native 0x0c] ++ (Aligned.counter value).fields]
  | .listHead slot keys _schema values =>
      [[.native 0x30], indexPathFields slot false keys, listIndexFields 0,
        [.native 0x0c] ++ (Aligned.nativeFields values).fields]
  | .listPushFront slot keys _ values =>
      [indexPathFields slot true keys, [.native 0x30], listIndexFields 2,
        [.native 0x0e, .native 1], listNodePushFields values, [.native 0x40],
        listU8CellPushFields 2, [.native 0x40], [.native 0x91], [.native 0x40],
        listU8CellPushFields 1, [.native 0x40], [.native (0x90 + keys.length + 2)]]
  | .listPopFront slot keys =>
      [indexPathFields slot true keys, [.native 0x30], listIndexFields 2,
        [.native 0x0f, .native 1], [.native 0x0b], listIndexFields 1,
        [.native (0x90 + keys.length + 1)]]
  | .listReset slot [] =>
      [[.native 0x10, .native 1] ++ (Aligned.field (.native slot)).fields,
        emptyListPushFields, [.native 0x91]]
  | .listReset slot keys =>
      match keys.getLast? with
      | none => []
      | some finalKey =>
        let parents := keys.take (keys.length - 1)
        [indexPathFields slot true parents,
          [.native 0x10, .native 1] ++ finalKey.fields,
          emptyListPushFields, [.native (0x90 + keys.length + 1)]]
  | .mapRemove slot keys =>
      match keys.getLast? with
      | none => []
      | some finalKey =>
        let parents := keys.take (keys.length - 1)
        [indexPathFields slot true parents,
          [.native 0x10, .native 1] ++ finalKey.fields,
          [.native 0x19], [.native (0x90 + keys.length)]]
  | operation => [operation.fields]

structure Read where
  name : String
  ty : Ty
  components : List (String × Ty) := []
  schema : Option Lean.Json := none
  /-- Source guard for a conditionally bound read. Inactive reads use zero. -/
  guard : Option (Expr .bool) := none

def Read.inactiveDefaultConstraint (read : Read) : Option (Expr .bool) :=
  if !read.components.isEmpty then none else
  match read.ty, read.guard with
  | .bytes _, _ | .jubjubScalar, _ | .jubjubPoint, _ | .foreign _, _ | _, none => none
  | .native, some guard => some (.eq (.ref read.name) (.select guard (.ref read.name) (.native 0)))
  | .bool, some guard => some (.eq (.ref read.name) (.select guard (.ref read.name) (.bool false)))
  | .uint maximum, some guard => some (.eq (.ref read.name)
      (.select guard (.ref read.name) (.uint maximum 0)))

def Read.bindings (read : Read) : List (String × Ty) :=
  if read.components.isEmpty then [(read.name, read.ty)] else read.components

def Read.inactiveDefaultConstraints (read : Read) : List (Expr .bool) :=
  if read.components.isEmpty then read.inactiveDefaultConstraint.toList else
  match read.guard with
  | none => []
  | some guard => read.components.filterMap fun (name, type) =>
      match type with
      | .native => some (.eq (.ref name) (.select guard (.ref name) (.native 0)))
      | .bool => some (.eq (.ref name) (.select guard (.ref name) (.bool false)))
      | .uint maximum => some (.eq (.ref name) (.select guard (.ref name) (.uint maximum 0)))
      | .bytes _ | .jubjubScalar | .jubjubPoint | .foreign _ => none

structure Plan where
  operations : List Op := []
  /-- Optional source activity guard per opcode group. Empty means all groups
  are active, preserving historical plans. -/
  activityGuards : List (Option (Expr .bool)) := []
  reads : List Read := []
  guards : List (Expr .bool) := []

def Plan.fields (plan : Plan) : List Scalar := plan.operations.flatMap Op.fields

def Plan.fieldGroups (plan : Plan) : List (List Scalar) :=
  plan.operations.flatMap Op.fieldGroups

/-- Public byte inputs are exposed to the pinned native transcript as one
field-aligned UInt8 projection per source byte. -/
def byteProjectionName (input : String) (index : Nat) : String :=
  s!"_noctium_bytes_{input}_{index}"

def jubjubScalarProjectionName (input : String) : String :=
  s!"_noctium_jubjub_scalar_{input}"

def jubjubPointProjectionName (input : String) (index : Nat) : String :=
  s!"_noctium_jubjub_point_{input}_{index}"

def publicInputReadCount (inputs : List Input) : Nat :=
  inputs.foldl (fun count input =>
    if input.visibility != .«public» then count
    else count + match input.ty with
      | .bytes length => length
      | .jubjubPoint => 2
      | .foreign kind => kind.encodedFieldCount
      | _ => 1) 0

/-- Generated field expressions must retain the source/read types even though
their native representation is uniformly a field. -/
def Plan.validate (plan : Plan) (entry : Entrypoint) : Except String Unit := do
  let publicCount := publicInputReadCount entry.circuit.inputs
  let env := entry.circuit.inputs.map (fun input => (input.name, input.ty)) ++
    entry.circuit.outputs.map (fun output => (output.name, output.ty)) ++
    (plan.reads.drop publicCount).flatMap Read.bindings
  for field in plan.fields do field.validate expressionCapabilities env
  for guard in plan.guards do guard.validate expressionCapabilities env
  unless plan.activityGuards.isEmpty || plan.activityGuards.length == plan.operations.length do
    throw "native activity guard schedule length mismatch"
  for guard in plan.activityGuards do
    if let some guard := guard then guard.validate expressionCapabilities env
  for read in plan.reads do
    if read.components.isEmpty != read.schema.isNone then
      throw "native composite read schema/component metadata mismatch"
    if !read.components.isEmpty then
      unless uniqueNames (read.components.map Prod.fst) do
        throw "duplicate native composite read field binding"
      unless read.components.all (fun component => component.2 == .native) do
        throw "native composite reads currently require Native fields"
    if let some guard := read.guard then guard.validate expressionCapabilities env

private def nativeValue : (ty : Ty) → Expr ty → Except String Scalar
  | .native, value => pure value
  | .bool, value => pure (.select value (.native 1) (.native 0))
  | .uint _, value => pure (.cast .native value)
  | .bytes _, _ => throw "Bytes32 requires byte alignment, not scalar conversion"
  | .jubjubScalar, _ | .jubjubPoint, _ | .foreign _, _ => throw "opaque values require explicit encoding projections"

private def nativeAligned : (ty : Ty) → Expr ty → Except String Aligned
  | .native, value => pure (.field value)
  | .bool, value => pure (.field (.select value (.native 1) (.native 0)))
  | .uint _, value => pure (.field (.cast .native value))
  | .bytes 32, value => pure (.bytes32 value)
  | .bytes _, _ => throw "unsupported byte alignment"
  | .jubjubScalar, _ | .jubjubPoint, _ | .foreign _, _ => throw "opaque values require explicit encoding projections"

private def nativeRead (ty : Ty) (name : String) : Except String Scalar :=
  match ty with
  | .native => pure (.ref name)
  | .bool => pure (.cast .native (.ref name : Expr .bool))
  | .uint maximum => pure (.cast .native (.ref name : Expr (.uint maximum)))
  | .bytes _ => throw "Bytes32 is read through byte alignment"
  | .jubjubScalar | .jubjubPoint | .foreign _ => throw "opaque inputs use reserved Native projections"

private def nativePathKeys (keys : List PathKey) : Except String (List Aligned) :=
  keys.mapM fun key => match key with
    | .mk ty value => nativeAligned ty value

private def compositeSchema (environment : Types.CompositeEnv) (type : Types.CompositeType) :
    Except String Lean.Json := do
  let compiled ← (Types.compileType environment type).mapError (·.message)
  Types.schemaJson compiled

private def splitPath (keys : List Aligned) : Except String (List Aligned × Aligned) := do
  if keys.isEmpty then throw "nested map path must contain at least one key"
  let some finalKey := keys.getLast? | throw "nested map path must contain at least one key"
  pure (keys.take (keys.length - 1), finalKey)

private def pathWriteOps (slot : Nat) (keys : List Aligned) (value : Aligned)
    (emptyMap : Bool) : Except String (List Op) := do
  let (parents, finalKey) ← splitPath keys
  let levels := keys.length + 1
  if levels >= 16 then throw "nested map insertion exceeds native Ins depth"
  let newValue := if emptyMap then
    [.push finalKey, .push (.field (.native 2)), .newMap]
  else [.push finalKey, .push value true]
  pure ([.indexPath slot true parents] ++ newValue ++ [.insert levels])

private def pathWriteCompositeOps (slot : Nat) (keys : List Aligned)
    (schema : Lean.Json) (values : List Scalar) : Except String (List Op) := do
  let (parents, finalKey) ← splitPath keys
  let levels := keys.length + 1
  if levels >= 16 then throw "nested map insertion exceeds native Ins depth"
  pure ([.indexPath slot true parents, .push finalKey,
    .pushFields schema values true, .insert levels])

private def stateSlot (state : List StateDecl) (name : String) : Except String Nat :=
  match state.findIdx? (·.name == name) with
  | some index => pure index
  | none => throw s!"unknown ledger state '{name}'"

private def resolveTreeState (state : List StateDecl) (name : String)
    (keys : List PathKey) : Except String LedgerValueType := do
  let some declaration := state.find? (·.name == name) | throw s!"unknown tree state '{name}'"
  let .tree schema := declaration.kind | throw s!"state '{name}' is not a recursive tree"
  schema.resolvePath keys

private def resolveCounterState (state : List StateDecl) (name : String)
    (keys : List PathKey) : Except String Unit := do
  let some declaration := state.find? (·.name == name) | throw s!"unknown Counter state '{name}'"
  let .tree schema := declaration.kind | throw s!"state '{name}' is not a recursive tree"
  schema.counterPath keys

private def resolveListState (state : List StateDecl) (name : String)
    (keys : List PathKey) :
    Except String (Types.CompositeEnv × Types.CompositeType × Types.CheckedLayout Types.defaultLimits) := do
  let some declaration := state.find? (·.name == name) | throw s!"unknown List state '{name}'"
  let .tree schema := declaration.kind | throw s!"state '{name}' is not a recursive tree"
  schema.listPath keys

private def expressionNames : Expr ty → List String
  | .native _ | .bool _ | .uint _ _ | .foreignBase _ _ | .foreignScalar _ _ | .foreignIdentity _ => []
  | .foreignEncodedField value _ => expressionNames value
  | .bytesField value _ | .bytesAt value _ => expressionNames value
  | .sha512 value | .keccak256 value | .persistentHash32 value => expressionNames value
  | .bytes32Literal _ | .bytesLiteral _ _ => []
  | .persistentHashVector32 values => values.flatMap expressionNames
  | .persistentHashNative value => expressionNames value
  | .hashToCurve values | .persistentHashNativeVector values => values.flatMap expressionNames
  | .toBytes32 value | .fromBytes32 value => expressionNames value
  | .reverseBytes32 value | .reverseBytes value | .sliceBytes value _ _ => expressionNames value
  | .concatBytes left right => expressionNames left ++ expressionNames right
  | .jubjubScalarFromNative value | .jubjubScalarToNative value
  | .jubjubMulGenerator value | .jubjubNeg value
  | .jubjubCoordinate value _ => expressionNames value
  | .jubjubMul point scalar | .jubjubAdd point scalar =>
    expressionNames point ++ expressionNames scalar
  | .jubjubFromCoordinates x y => expressionNames x ++ expressionNames y
  | .ref name => [name]
  | .boolAnd left right | .boolOr left right | .boolXor left right
  | .add left right => expressionNames left ++ expressionNames right
  | .mul left right => expressionNames left ++ expressionNames right
  | .sub left right => expressionNames left ++ expressionNames right
  | .uadd left right => expressionNames left ++ expressionNames right
  | .usub left right => expressionNames left ++ expressionNames right
  | .umul left right => expressionNames left ++ expressionNames right
  | .inv value => expressionNames value
  | .cast _ value => expressionNames value
  | .letE name value body => name :: (expressionNames value ++ expressionNames body)
  | .assertE condition body => expressionNames condition ++ expressionNames body
  | .disclose _ value => expressionNames value
  | .eq left right => expressionNames left ++ expressionNames right
  | .select condition yes no =>
    expressionNames condition ++ expressionNames yes ++ expressionNames no
  | .poseidon2 _ left right => expressionNames left ++ expressionNames right

private def pathExpressionNames (keys : List PathKey) : List String :=
  keys.flatMap fun key => match key with
    | .mk _ value => expressionNames value

private def freshActivityName (names : List String) : String :=
  let longest := names.foldl (fun length name => max length name.length) 0
  "_noctium_activity_guard_" ++ String.ofList (List.replicate (longest + 1) 'x')

private def zeroValue : (ty : Ty) → Option (Expr ty)
  | .native => some (.native 0)
  | .bool => some (.bool false)
  | .uint maximum => some (.uint maximum 0)
  | .bytes 32 => some (.bytes32Literal (List.replicate 32 0))
  | .bytes length => some (.bytesLiteral length (List.replicate length 0))
  | .jubjubScalar => some (.jubjubScalarFromNative (.native 0))
  | .jubjubPoint => some (.jubjubFromCoordinates (.native 0) (.native 1))
  | .foreign (.base curve) => some (.foreignBase curve 0)
  | .foreign (.scalar curve) => some (.foreignScalar curve 0)
  | .foreign (.point curve) => some (.foreignIdentity curve)

private def castMayFail (target source : Ty) : Bool :=
  match target, source with
  | .uint _, .native => true
  | .uint maximum, .uint sourceMaximum => sourceMaximum > maximum
  | .uint maximum, .bool => maximum < 1
  | _, _ => false

/-- Replace every partial scalar operation with a safe inactive computation.
The native source guard is a collision-free outer let binding, so nested source
lets cannot capture its references. Eager selects still evaluate both arms. -/
private def totalizeUnder (guard : Expr .bool) : Expr ty → Expr ty
  | .foreignBase curve value => .foreignBase curve value
  | .foreignScalar curve value => .foreignScalar curve value
  | .foreignIdentity curve => .foreignIdentity curve
  | .foreignEncodedField value index => .foreignEncodedField (totalizeUnder guard value) index
  | .native value => .native value
  | .bool value => .bool value
  | .boolAnd left right => .boolAnd (totalizeUnder guard left) (totalizeUnder guard right)
  | .boolOr left right => .boolOr (totalizeUnder guard left) (totalizeUnder guard right)
  | .boolXor left right => .boolXor (totalizeUnder guard left) (totalizeUnder guard right)
  | .uint maximum value => .uint maximum value
  | .bytesField value index => .bytesField (totalizeUnder guard value) index
  | .bytesAt value index => .bytesAt (totalizeUnder guard value) index
  | .sha512 value => .sha512 (totalizeUnder guard value)
  | .keccak256 value => .keccak256 (totalizeUnder guard value)
  | .persistentHash32 value => .persistentHash32 (totalizeUnder guard value)
  | .bytes32Literal values => .bytes32Literal values
  | .bytesLiteral length values => .bytesLiteral length values
  | .reverseBytes value => .reverseBytes (totalizeUnder guard value)
  | .sliceBytes value start end_ => .sliceBytes (totalizeUnder guard value) start end_
  | .concatBytes left right => .concatBytes (totalizeUnder guard left) (totalizeUnder guard right)
  | .persistentHashVector32 values => .persistentHashVector32 (values.map (totalizeUnder guard))
  | .persistentHashNative value => .persistentHashNative (totalizeUnder guard value)
  | .persistentHashNativeVector values => .persistentHashNativeVector (values.map (totalizeUnder guard))
  | .hashToCurve values => .hashToCurve (values.map (totalizeUnder guard))
  | .toBytes32 value => .toBytes32 (totalizeUnder guard value)
  | .reverseBytes32 value => .reverseBytes32 (totalizeUnder guard value)
  | .fromBytes32 (target := .jubjubPoint) value =>
    let identity : Expr (.bytes 32) := .bytes32Literal (1 :: List.replicate 31 0)
    .fromBytes32 (.select guard (totalizeUnder guard value) identity)
  | .fromBytes32 value => .fromBytes32 (totalizeUnder guard value)
  | .jubjubScalarFromNative value => .jubjubScalarFromNative (totalizeUnder guard value)
  | .jubjubScalarToNative value => .jubjubScalarToNative (totalizeUnder guard value)
  | .jubjubMulGenerator scalar => .jubjubMulGenerator (totalizeUnder guard scalar)
  | .jubjubMul point scalar =>
    .jubjubMul (totalizeUnder guard point) (totalizeUnder guard scalar)
  | .jubjubAdd left right =>
    .jubjubAdd (totalizeUnder guard left) (totalizeUnder guard right)
  | .jubjubNeg point => .jubjubNeg (totalizeUnder guard point)
  | .jubjubCoordinate point index => .jubjubCoordinate (totalizeUnder guard point) index
  | .jubjubFromCoordinates x y => .jubjubFromCoordinates
      (.select guard (totalizeUnder guard x) (.native 0))
      (.select guard (totalizeUnder guard y) (.native 1))
  | .ref name => .ref name
  | .add left right => .add (totalizeUnder guard left) (totalizeUnder guard right)
  | .mul left right => .mul (totalizeUnder guard left) (totalizeUnder guard right)
  | .sub left right => .sub (totalizeUnder guard left) (totalizeUnder guard right)
  | .uadd left right => .uadd (totalizeUnder guard left) (totalizeUnder guard right)
  | .usub (m := m) (n := n) left right =>
    .usub
      (.select guard (totalizeUnder guard left) (.uint m 0))
      (.select guard (totalizeUnder guard right) (.uint n 0))
  | .umul left right => .umul (totalizeUnder guard left) (totalizeUnder guard right)
  | .inv (ty := .native) value =>
    .inv (.select guard (totalizeUnder guard value) (.native 1))
  | .inv (ty := .jubjubScalar) value =>
    .inv (.jubjubScalarFromNative
      (.select guard (.jubjubScalarToNative (totalizeUnder guard value)) (.native 1)))
  | .inv value => .inv (totalizeUnder guard value)
  | .cast target (source := source) value =>
    let value := totalizeUnder guard value
    if castMayFail target source then
      match zeroValue source with
      | some zero => .cast target (.select guard value zero)
      | none => .cast target value
    else .cast target value
  | .letE name value body =>
    .letE name (totalizeUnder guard value) (totalizeUnder guard body)
  | .assertE condition body =>
    .assertE (.select guard (totalizeUnder guard condition) (.bool true))
      (totalizeUnder guard body)
  | .disclose span value => .disclose span (totalizeUnder guard value)
  | .eq left right => .eq (totalizeUnder guard left) (totalizeUnder guard right)
  | .select condition yes no =>
    .select (totalizeUnder guard condition) (totalizeUnder guard yes) (totalizeUnder guard no)
  | .poseidon2 domain left right =>
    .poseidon2 domain (totalizeUnder guard left) (totalizeUnder guard right)

private def totalizeActivityValue (guard : Expr .bool) (avoid : List String)
    (value : Expr ty) : Expr ty :=
  let name := freshActivityName (avoid ++ expressionNames guard ++ expressionNames value)
  .letE name guard (totalizeUnder (.ref name) value)

private def totalizePathKeys (condition : Expr .bool) (keys : List PathKey) : List PathKey :=
  let avoid := pathExpressionNames keys
  keys.map fun key => match key with
    | .mk .native value =>
      let guardName := freshActivityName (avoid ++ expressionNames condition ++ expressionNames value)
      let guardedValue := totalizeUnder (.ref guardName) value
      .mk .native (.letE guardName condition
        (.select (.ref guardName) guardedValue (.native 0)))
    | .mk .bool value =>
      let guardName := freshActivityName (avoid ++ expressionNames condition ++ expressionNames value)
      let guardedValue := totalizeUnder (.ref guardName) value
      .mk .bool (.letE guardName condition
        (.select (.ref guardName) guardedValue (.bool false)))
    | .mk (.uint maximum) value =>
      let guardName := freshActivityName (avoid ++ expressionNames condition ++ expressionNames value)
      let guardedValue := totalizeUnder (.ref guardName) value
      .mk (.uint maximum) (.letE guardName condition
        (.select (.ref guardName) guardedValue (.uint maximum 0)))
    | .mk (.bytes 32) value =>
      let guardName := freshActivityName (avoid ++ expressionNames condition ++ expressionNames value)
      let guardedValue := totalizeUnder (.ref guardName) value
      .mk (.bytes 32) (.letE guardName condition (.select (.ref guardName) guardedValue
        (.bytes32Literal (List.replicate 32 0))))
    | .mk (.bytes length) value =>
      let guardName := freshActivityName (avoid ++ expressionNames condition ++ expressionNames value)
      let guardedValue := totalizeUnder (.ref guardName) value
      .mk (.bytes length) (.letE guardName condition (.select (.ref guardName) guardedValue
        (.bytesLiteral length (List.replicate length 0))))
    | .mk ty value =>
      let guardName := freshActivityName (avoid ++ expressionNames condition ++ expressionNames value)
      .mk ty (.letE guardName condition (totalizeUnder (.ref guardName) value))

private def totalizeActivityCondition (guard condition : Expr .bool) : Expr .bool :=
  let name := freshActivityName (expressionNames guard ++ expressionNames condition)
  .letE name guard
    (.select (.ref name) (totalizeUnder (.ref name) condition) (.bool true))

/-- Evaluate a nested branch condition only when its enclosing branch is active.
The inactive arm becomes false, and partial condition expressions are totalized
under the captured parent guard before eager `select` lowering. -/
def activityGuardWithin (parent condition : Expr .bool) : Expr .bool :=
  let name := freshActivityName (expressionNames parent ++ expressionNames condition)
  .letE name parent
    (.select (.ref name) (totalizeUnder (.ref name) condition) (.bool false))

/-- One effect in the production ordered ledger plan. The current read count
fixes generated absence names and therefore belongs to the accumulator. -/
def appendEffect (state : List StateDecl) (effect : Effect)
    (plan : Plan) : Except String Plan := do
  match effect with
  | .readCell name destination ty =>
    let slot ← stateSlot state name
    let value ← nativeRead ty destination
    pure { plan with
      operations := plan.operations ++ [.dup, .index slot, .popeq (.field value)]
      reads := plan.reads ++ [{name := destination, ty}] }
  | .require condition =>
    pure {plan with guards := plan.guards ++ [condition]}
  | .requireAbsent name _ key =>
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    let readName := s!"_noctium_absence_{plan.reads.length}"
    pure { plan with
      operations := plan.operations ++ [
        .dup, .index slot, .push key, .member, .popeq (.bit false)]
      reads := plan.reads ++ [{name := readName, ty := .bool}]
      guards := plan.guards ++ [.eq (.ref readName : Expr .bool) (.bool false)] }
  | .writeCell name _ value =>
    let slot ← stateSlot state name
    let value ← nativeValue _ value
    pure {plan with operations := plan.operations ++ [
      .push (.field (.native slot)), .push (.field value) true, .insert 1]}
  | .writeMap name _ _ key value =>
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    let value ← nativeValue _ value
    pure {plan with operations := plan.operations ++ [
      .index slot true, .push key,
      .push (.field value) true, .insert 2]}
  | .readMap name destination _ ty key => do
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    let value ← nativeRead ty destination
    pure { plan with
      operations := plan.operations ++ [
        .dup, .mapIndex slot key,
        .popeq (.field value)]
      reads := plan.reads ++ [{name := destination, ty}] }
  | .readMember name destination _ _ key => do
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    pure { plan with
      operations := plan.operations ++ [
        .dup, .index slot, .push key, .member,
        .popeq (.bitExpr (.ref destination))]
      reads := plan.reads ++ [{name := destination, ty := .bool}] }
  | .readPath name destination keys ty => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let value ← nativeRead ty destination
    pure {plan with
      operations := plan.operations ++ [.dup, .indexPath slot false keys, .popeq (.field value)]
      reads := plan.reads ++ [{name := destination, ty}]}
  | .counterRead name destination keys => do
    let slot ← stateSlot state name
    resolveCounterState state name keys
    let keys ← nativePathKeys keys
    let value : Expr (.uint (2 ^ 64 - 1)) := .ref destination
    pure {plan with
      operations := plan.operations ++ [.dup, .indexPath slot false keys, .popeq (.counter value)]
      reads := plan.reads ++ [{name := destination, ty := .uint (2 ^ 64 - 1)}]}
  | .listLength name destination keys => do
    let slot ← stateSlot state name
    discard (resolveListState state name keys)
    let alignedKeys ← nativePathKeys keys
    let value : Expr (.uint (2 ^ 64 - 1)) := .ref destination
    pure {plan with
      operations := plan.operations ++ [.listLength slot alignedKeys value]
      reads := plan.reads ++ [{name := destination, ty := .uint (2 ^ 64 - 1)}]}
  | .listHead name destination keys type destinations => do
    let slot ← stateSlot state name
    let (environment, foundType, _) ← resolveListState state name keys
    unless foundType == type do throw "List head record type mismatch"
    let names ← LedgerValueType.nativeLeafNames environment type
    unless names.length == destinations.length do throw "List head destination count mismatch"
    let alignedKeys ← nativePathKeys keys
    let schema ← compositeSchema environment type
    let values := destinations.map fun field => Expr.ref (ty := .native) field
    let components := destinations.map fun field => (field, Ty.native)
    let read : Read := {name := destination, ty := Ty.native, components := components, schema := some schema}
    pure {plan with
      operations := plan.operations ++ [.listHead slot alignedKeys schema values]
      reads := plan.reads ++ [read]}
  | .listPushFront name keys type values => do
    let slot ← stateSlot state name
    let (environment, foundType, _) ← resolveListState state name keys
    unless foundType == type do throw "List push record type mismatch"
    let names ← LedgerValueType.nativeLeafNames environment type
    unless names.length == values.length do throw "List push record leaf count mismatch"
    let alignedKeys ← nativePathKeys keys
    let schema ← compositeSchema environment type
    pure {plan with operations := plan.operations ++ [
      .listPushFront slot alignedKeys schema values]}
  | .listPopFront name keys => do
    let slot ← stateSlot state name
    discard (resolveListState state name keys)
    let alignedKeys ← nativePathKeys keys
    pure {plan with operations := plan.operations ++ [.listPopFront slot alignedKeys]}
  | .listReset name keys => do
    let slot ← stateSlot state name
    discard (resolveListState state name keys)
    let alignedKeys ← nativePathKeys keys
    pure {plan with operations := plan.operations ++ [.listReset slot alignedKeys]}
  | .removePath name keys => do
    let slot ← stateSlot state name
    let some declaration := state.find? (·.name == name)
      | throw s!"unknown tree state '{name}'"
    let .tree schema := declaration.kind
      | throw s!"state '{name}' is not a recursive map"
    schema.removalPath keys
    let alignedKeys ← nativePathKeys keys
    pure {plan with operations := plan.operations ++ [.mapRemove slot alignedKeys]}
  | .readCompositePath name destination keys type destinations => do
    let slot ← stateSlot state name
    let .composite environment foundType ← resolveTreeState state name keys
      | throw "nested composite read must select a composite value"
    unless foundType == type do throw "nested composite read type mismatch"
    let names ← LedgerValueType.nativeLeafNames environment type
    unless names.length == destinations.length do throw "nested composite read destination count mismatch"
    let alignedKeys ← nativePathKeys keys
    let schema ← compositeSchema environment type
    let values := destinations.map fun name => Expr.ref (ty := .native) name
    let components := destinations.map fun name => (name, Ty.native)
    pure {plan with
      operations := plan.operations ++ [
        .dup, .indexPath slot false alignedKeys, .popeqFields schema values]
      reads := plan.reads ++ [{name := destination, ty := .native, components := components, schema := some schema}]}
  | .memberPath name destination keys => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let (parents, finalKey) ← splitPath keys
    pure {plan with
      operations := plan.operations ++ [
        .dup, .indexPath slot false parents, .push finalKey, .member,
        .popeq (.bitExpr (.ref destination))]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .insertPath name keys ty value | .writePath name keys ty value => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let value ← nativeAligned ty value
    let operations ← pathWriteOps slot keys value false
    pure {plan with operations := plan.operations ++ operations}
  | .writeCompositePath name keys type values => do
    let slot ← stateSlot state name
    let .composite environment foundType ← resolveTreeState state name keys
      | throw "nested composite write must select a composite value"
    unless foundType == type do throw "nested composite write type mismatch"
    let names ← LedgerValueType.nativeLeafNames environment type
    unless names.length == values.length do throw "nested composite write leaf count mismatch"
    let alignedKeys ← nativePathKeys keys
    let schema ← compositeSchema environment type
    let operations ← pathWriteCompositeOps slot alignedKeys schema values
    pure {plan with operations := plan.operations ++ operations}
  | .counterAdjust name keys subtract amount => do
    let slot ← stateSlot state name
    resolveCounterState state name keys
    let alignedKeys ← nativePathKeys keys
    let operation := if subtract then Op.subImmediate amount else Op.addImmediate amount
    pure {plan with operations := plan.operations ++ [
      .indexPath slot true alignedKeys, operation, .insert (keys.length + 1)]}
  | .counterReset name keys => do
    let slot ← stateSlot state name
    resolveCounterState state name keys
    if keys.isEmpty then
      let value : Expr (.uint (2 ^ 64 - 1)) := .uint (2 ^ 64 - 1) 0
      pure {plan with operations := plan.operations ++ [
        .push (.field (.native slot)), .push (.counter value) true, .insert 1]}
    else
      let alignedKeys ← nativePathKeys keys
      let value : Expr (.uint (2 ^ 64 - 1)) := .uint (2 ^ 64 - 1) 0
      let operations ← pathWriteOps slot alignedKeys (.counter value) false
      pure {plan with operations := plan.operations ++ operations}
  | .emptyMapPath name keys => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let operations ← pathWriteOps slot keys (.field (.native 2)) true
    pure {plan with operations := plan.operations ++ operations}

def appendEffects (state : List StateDecl) (effects : List Effect)
    (initial : Plan) : Except String Plan :=
  effects.foldlM (fun plan effect => appendEffect state effect plan) initial

/-- Lower one source effect. Writes bind their opcode groups to the activity
guard. Guarded requirements become assertions with no VM operation groups. -/
private def appendEffectWithActivity (state : List StateDecl) (effect : Effect)
    (guard : Option (Expr .bool)) (plan : Plan) : Except String Plan := do
  let loweredEffect ← match guard, effect with
    | none, _ => pure effect
    | some condition, .writeCell name ty value =>
      pure (.writeCell name ty (totalizeActivityValue condition [] value))
    | some condition, .writeMap name keyTy valueTy key value =>
      let avoid := expressionNames key ++ expressionNames value
      pure (.writeMap name keyTy valueTy
        (totalizeActivityValue condition avoid key)
        (totalizeActivityValue condition avoid value))
    | some condition, .readMap name destination keyTy valueTy key =>
      pure (.readMap name destination keyTy valueTy
        (totalizeActivityValue condition (expressionNames key) key))
    | some condition, .readMember name destination keyTy valueTy key =>
      pure (.readMember name destination keyTy valueTy
        (totalizeActivityValue condition (expressionNames key) key))
    | some condition, .readPath name destination keys ty =>
      pure (.readPath name destination (totalizePathKeys condition keys) ty)
    | some condition, .readCompositePath name destination keys type destinations =>
      pure (.readCompositePath name destination (totalizePathKeys condition keys) type destinations)
    | some condition, .memberPath name destination keys =>
      pure (.memberPath name destination (totalizePathKeys condition keys))
    | some condition, .counterRead name destination keys =>
      pure (.counterRead name destination (totalizePathKeys condition keys))
    | some condition, .counterAdjust name keys subtract amount =>
      pure (.counterAdjust name (totalizePathKeys condition keys) subtract amount)
    | some condition, .counterReset name keys =>
      pure (.counterReset name (totalizePathKeys condition keys))
    | some condition, .listLength name destination keys =>
      pure (.listLength name destination (totalizePathKeys condition keys))
    | some condition, .listHead name destination keys type destinations =>
      pure (.listHead name destination (totalizePathKeys condition keys) type destinations)
    | some condition, .listPushFront name keys type values =>
      let avoid := pathExpressionNames keys ++ values.flatMap expressionNames
      pure (.listPushFront name (totalizePathKeys condition keys) type
        (values.map (totalizeActivityValue condition avoid)))
    | some condition, .listPopFront name keys =>
      pure (.listPopFront name (totalizePathKeys condition keys))
    | some condition, .listReset name keys =>
      pure (.listReset name (totalizePathKeys condition keys))
    | some condition, .removePath name keys =>
      pure (.removePath name (totalizePathKeys condition keys))
    | some condition, .insertPath name keys ty value =>
      let avoid := pathExpressionNames keys ++ expressionNames value
      pure (.insertPath name (totalizePathKeys condition keys) ty
        (totalizeActivityValue condition avoid value))
    | some condition, .writePath name keys ty value =>
      let avoid := pathExpressionNames keys ++ expressionNames value
      pure (.writePath name (totalizePathKeys condition keys) ty
        (totalizeActivityValue condition avoid value))
    | some condition, .writeCompositePath name keys type values =>
      let avoid := pathExpressionNames keys ++ values.flatMap expressionNames
      pure (.writeCompositePath name (totalizePathKeys condition keys) type
        (values.map (totalizeActivityValue condition avoid)))
    | some condition, .emptyMapPath name keys =>
      pure (.emptyMapPath name (totalizePathKeys condition keys))
    | some _, .readCell .. => pure effect
    | some condition, .require required =>
      pure (.require (totalizeActivityCondition condition required))
    | some _, _ => throw "native guards are supported only on ledger reads, writes, and require effects"
  let before := plan.operations.length
  let result ← appendEffect state loweredEffect plan
  let added := result.operations.length - before
  match guard, effect with
  | some _, .require _ => pure result
  | some condition, .readCell .. | some condition, .readMap .. | some condition, .readMember .. =>
    let readIndex := plan.reads.length
    let some read := result.reads[readIndex]? | throw "guarded read did not append a read binding"
    let reads := result.reads.take readIndex ++ [{read with guard := some condition}]
    let priorGuards := if plan.activityGuards.isEmpty then List.replicate before none
      else plan.activityGuards
    pure {result with
      reads := reads
      activityGuards := priorGuards ++ List.replicate added (some condition)}
  | some condition, .readPath .. | some condition, .readCompositePath .. |
      some condition, .memberPath .. | some condition, .counterRead .. |
      some condition, .listLength .. | some condition, .listHead .. =>
    let readIndex := plan.reads.length
    let some read := result.reads[readIndex]? | throw "guarded nested read did not append a read binding"
    let reads := result.reads.take readIndex ++ [{read with guard := some condition}]
    let priorGuards := if plan.activityGuards.isEmpty then List.replicate before none
      else plan.activityGuards
    pure {result with
      reads := reads
      activityGuards := priorGuards ++ List.replicate added (some condition)}
  | some condition, .writeCell .. | some condition, .writeMap .. =>
    let priorGuards := if plan.activityGuards.isEmpty then List.replicate before none
      else plan.activityGuards
    pure {result with activityGuards := priorGuards ++ List.replicate added (some condition)}
  | some condition, .insertPath .. | some condition, .writePath .. |
      some condition, .writeCompositePath .. | some condition, .emptyMapPath .. |
      some condition, .counterAdjust .. | some condition, .counterReset .. |
      some condition, .listPushFront .. | some condition, .listPopFront .. |
      some condition, .listReset .. | some condition, .removePath .. =>
    let priorGuards := if plan.activityGuards.isEmpty then List.replicate before none
      else plan.activityGuards
    pure {result with activityGuards := priorGuards ++ List.replicate added (some condition)}
  | none, _ =>
    if plan.activityGuards.isEmpty then pure result
    else
      let priorGuards := plan.activityGuards
      pure {result with activityGuards := priorGuards ++ List.replicate added none}
  | some _, _ => throw "native guards are supported only on ledger reads, writes, and require effects"

/-- Lower ordered effects while keeping optional activity guards aligned with
each emitted opcode group. -/
def appendEffectsGuarded (state : List StateDecl) (effects : List Effect)
    (guards : List (Option (Expr .bool))) (initial : Plan) : Except String Plan := do
  unless guards.isEmpty || guards.length == effects.length do
    throw "effect guard metadata length mismatch"
  let mut plan := initial
  for (effect, index) in effects.zipIdx do
    plan ← appendEffectWithActivity state effect (guards[index]?.getD none) plan
  pure plan

private def publicInputStep (input : Input) (plan : Plan) : Except String Plan := do
  if input.visibility != .«public» then return plan
  match input.ty with
  | .bytes length =>
    let mut result := plan
    for index in List.range length do
      let bytes : Expr (.bytes length) := .ref input.name
      let byte : Expr (.uint 255) := .bytesAt bytes index
      let value := Aligned.field (.cast .native byte)
      let name := byteProjectionName input.name index
      result := { result with
        operations := result.operations ++ [.push value, .popeq value]
        reads := result.reads ++ [{name, ty := .uint 255}] }
    pure result
  | .jubjubScalar => do
    let scalar : Expr .jubjubScalar := .ref input.name
    let value := Aligned.field (.jubjubScalarToNative scalar)
    let name := input.publicProjectionIdentifiers[0]!
    pure {plan with
      operations := plan.operations ++ [.push value, .popeq value]
      reads := plan.reads ++ [{name, ty := .native}]}
  | .jubjubPoint => do
    let point : Expr .jubjubPoint := .ref input.name
    let mut result := plan
    for index in [0, 1] do
      let value := Aligned.field (.jubjubCoordinate point index)
      let name := input.publicProjectionIdentifiers[index]!
      result := {result with
        operations := result.operations ++ [.push value, .popeq value]
        reads := result.reads ++ [{name, ty := .native}]}
    pure result
  | .foreign kind => do
    let value : Expr (.foreign kind) := .ref input.name
    let mut result := plan
    for index in List.range kind.encodedFieldCount do
      let aligned := Aligned.field (.foreignEncodedField value index)
      let name := input.publicProjectionIdentifiers[index]!
      result := {result with
        operations := result.operations ++ [.push aligned, .popeq aligned]
        reads := result.reads ++ [{name, ty := .native}]}
    pure result
  | .native | .bool | .uint _ => do
    let value := Aligned.field (← nativeRead input.ty input.name)
    pure { plan with
      operations := plan.operations ++ [.push value, .popeq value]
      reads := plan.reads ++ [{name := input.name, ty := input.ty}] }

private def appendPublicInput := publicInputStep

/-- The exact public-input prefix used before source effects. -/
def publicInputPlan (inputs : List Input) (initial : Plan := {}) : Except String Plan :=
  inputs.foldlM (fun plan input => appendPublicInput input plan) initial

private def previousPublicInputStep (input : Input) (plan : Plan) : Except String Plan :=
  publicInputStep input plan

private def previousPublicInputLoop (inputs : List Input) (initial : Plan) : Except String Plan := do
  let mut plan := initial
  for input in inputs do
    plan ← previousPublicInputStep input plan
  pure plan

/-- The old mutable public-input loop equals the production pure prefix for
all input lists and starting plans. -/
theorem previousPublicInputLoop_eq_publicInputPlan (inputs : List Input)
    (initial : Plan) :
    previousPublicInputLoop inputs initial = publicInputPlan inputs initial := by
  unfold previousPublicInputLoop
  simp only [bind_pure]
  change (forIn inputs initial (fun input plan => do
      let result ← previousPublicInputStep input plan
      pure (ForInStep.yield result))) =
    inputs.foldlM (fun plan input => appendPublicInput input plan) initial
  have stepEq (input : Input) (plan : Plan) :
      (do let result ← previousPublicInputStep input plan
          pure (ForInStep.yield result)) =
        ForInStep.yield <$> previousPublicInputStep input plan := by
    cases previousPublicInputStep input plan <;> rfl
  simp only [stepEq]
  rw [List.forIn_yield_eq_foldlM]
  simp only [previousPublicInputStep, appendPublicInput]
  have mapIdentity (plan : Plan) (input : Input) :
      (fun result : Plan => result) <$> publicInputStep input plan =
        publicInputStep input plan := by
    cases publicInputStep input plan <;> rfl
  simp only [mapIdentity]

/-- Imperative counterpart retained for the kernel equivalence check. -/
private def previousEffectStep (state : List StateDecl) (effect : Effect)
    (initial : Plan) : Except String Plan := do
  let mut plan := initial
  match effect with
  | .readCell name destination ty =>
    let slot ← stateSlot state name
    let value ← nativeRead ty destination
    plan := { plan with
      operations := plan.operations ++ [.dup, .index slot, .popeq (.field value)]
      reads := plan.reads ++ [{name := destination, ty}] }
  | .require condition =>
    plan := {plan with guards := plan.guards ++ [condition]}
  | .requireAbsent name _ key =>
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    let name := s!"_noctium_absence_{plan.reads.length}"
    plan := { plan with
      operations := plan.operations ++ [
        .dup, .index slot, .push key, .member, .popeq (.bit false)]
      reads := plan.reads ++ [{name, ty := .bool}]
      guards := plan.guards ++ [.eq (.ref name : Expr .bool) (.bool false)] }
  | .writeCell name _ value =>
    let slot ← stateSlot state name
    let value ← nativeValue _ value
    plan := {plan with operations := plan.operations ++ [
      .push (.field (.native slot)), .push (.field value) true, .insert 1]}
  | .writeMap name _ _ key value =>
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    let value ← nativeValue _ value
    plan := {plan with operations := plan.operations ++ [
      .index slot true, .push key,
      .push (.field value) true, .insert 2]}
  | .readMap name destination _ ty key => do
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    let value ← nativeRead ty destination
    plan := { plan with
      operations := plan.operations ++ [
        .dup, .mapIndex slot key,
        .popeq (.field value)]
      reads := plan.reads ++ [{name := destination, ty}] }
  | .readMember name destination _ _ key => do
    let slot ← stateSlot state name
    let key ← nativeAligned _ key
    plan := { plan with
      operations := plan.operations ++ [
        .dup, .index slot, .push key, .member,
        .popeq (.bitExpr (.ref destination))]
      reads := plan.reads ++ [{name := destination, ty := .bool}] }
  | .readPath name destination keys ty => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let value ← nativeRead ty destination
    plan := {plan with
      operations := plan.operations ++ [.dup, .indexPath slot false keys, .popeq (.field value)]
      reads := plan.reads ++ [{name := destination, ty}]}
  | .counterRead name destination keys => do
    let slot ← stateSlot state name
    resolveCounterState state name keys
    let keys ← nativePathKeys keys
    let value : Expr (.uint (2 ^ 64 - 1)) := .ref destination
    plan := {plan with
      operations := plan.operations ++ [.dup, .indexPath slot false keys, .popeq (.counter value)]
      reads := plan.reads ++ [{name := destination, ty := .uint (2 ^ 64 - 1)}]}
  | .listLength name destination keys => do
    let slot ← stateSlot state name
    discard (resolveListState state name keys)
    let alignedKeys ← nativePathKeys keys
    let value : Expr (.uint (2 ^ 64 - 1)) := .ref destination
    plan := {plan with
      operations := plan.operations ++ [.listLength slot alignedKeys value]
      reads := plan.reads ++ [{name := destination, ty := .uint (2 ^ 64 - 1)}]}
  | .listHead name destination keys type destinations => do
    let slot ← stateSlot state name
    let (environment, foundType, _) ← resolveListState state name keys
    unless foundType == type do throw "List head record type mismatch"
    let names ← LedgerValueType.nativeLeafNames environment type
    unless names.length == destinations.length do throw "List head destination count mismatch"
    let alignedKeys ← nativePathKeys keys
    let schema ← compositeSchema environment type
    let values := destinations.map fun field => Expr.ref (ty := .native) field
    let components := destinations.map fun field => (field, Ty.native)
    let read : Read := {name := destination, ty := Ty.native, components := components, schema := some schema}
    plan := {plan with
      operations := plan.operations ++ [.listHead slot alignedKeys schema values]
      reads := plan.reads ++ [read]}
  | .listPushFront name keys type values => do
    let slot ← stateSlot state name
    let (environment, foundType, _) ← resolveListState state name keys
    unless foundType == type do throw "List push record type mismatch"
    let names ← LedgerValueType.nativeLeafNames environment type
    unless names.length == values.length do throw "List push record leaf count mismatch"
    let alignedKeys ← nativePathKeys keys
    let schema ← compositeSchema environment type
    plan := {plan with operations := plan.operations ++ [
      .listPushFront slot alignedKeys schema values]}
  | .listPopFront name keys => do
    let slot ← stateSlot state name
    discard (resolveListState state name keys)
    let alignedKeys ← nativePathKeys keys
    plan := {plan with operations := plan.operations ++ [.listPopFront slot alignedKeys]}
  | .listReset name keys => do
    let slot ← stateSlot state name
    discard (resolveListState state name keys)
    let alignedKeys ← nativePathKeys keys
    plan := {plan with operations := plan.operations ++ [.listReset slot alignedKeys]}
  | .readCompositePath name destination keys type destinations => do
    let slot ← stateSlot state name
    let .composite environment foundType ← resolveTreeState state name keys
      | throw "nested composite read must select a composite value"
    unless foundType == type do throw "nested composite read type mismatch"
    let names ← LedgerValueType.nativeLeafNames environment type
    unless names.length == destinations.length do throw "nested composite read destination count mismatch"
    let alignedKeys ← nativePathKeys keys
    let schema ← compositeSchema environment type
    let values := destinations.map fun name => Expr.ref (ty := .native) name
    let components := destinations.map fun name => (name, Ty.native)
    plan := {plan with
      operations := plan.operations ++ [
        .dup, .indexPath slot false alignedKeys, .popeqFields schema values]
      reads := plan.reads ++ [{name := destination, ty := .native, components := components, schema := some schema}]}
  | .memberPath name destination keys => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let (parents, finalKey) ← splitPath keys
    plan := {plan with
      operations := plan.operations ++ [
        .dup, .indexPath slot false parents, .push finalKey, .member,
        .popeq (.bitExpr (.ref destination))]
      reads := plan.reads ++ [{name := destination, ty := .bool}]}
  | .insertPath name keys ty value | .writePath name keys ty value => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let value ← nativeAligned ty value
    let operations ← pathWriteOps slot keys value false
    plan := {plan with operations := plan.operations ++ operations}
  | .writeCompositePath name keys type values => do
    let slot ← stateSlot state name
    let .composite environment foundType ← resolveTreeState state name keys
      | throw "nested composite write must select a composite value"
    unless foundType == type do throw "nested composite write type mismatch"
    let names ← LedgerValueType.nativeLeafNames environment type
    unless names.length == values.length do throw "nested composite write leaf count mismatch"
    let alignedKeys ← nativePathKeys keys
    let schema ← compositeSchema environment type
    let operations ← pathWriteCompositeOps slot alignedKeys schema values
    plan := {plan with operations := plan.operations ++ operations}
  | .counterAdjust name keys subtract amount => do
    let slot ← stateSlot state name
    resolveCounterState state name keys
    let alignedKeys ← nativePathKeys keys
    let operation := if subtract then Op.subImmediate amount else Op.addImmediate amount
    plan := {plan with operations := plan.operations ++ [
      .indexPath slot true alignedKeys, operation, .insert (keys.length + 1)]}
  | .counterReset name keys => do
    let slot ← stateSlot state name
    resolveCounterState state name keys
    if keys.isEmpty then
      let value : Expr (.uint (2 ^ 64 - 1)) := .uint (2 ^ 64 - 1) 0
      plan := {plan with operations := plan.operations ++ [
        .push (.field (.native slot)), .push (.counter value) true, .insert 1]}
    else
      let alignedKeys ← nativePathKeys keys
      let value : Expr (.uint (2 ^ 64 - 1)) := .uint (2 ^ 64 - 1) 0
      let operations ← pathWriteOps slot alignedKeys (.counter value) false
      plan := {plan with operations := plan.operations ++ operations}
  | .emptyMapPath name keys => do
    let slot ← stateSlot state name
    let keys ← nativePathKeys keys
    let operations ← pathWriteOps slot keys (.field (.native 2)) true
    plan := {plan with operations := plan.operations ++ operations}
  | .removePath name keys => do
    let slot ← stateSlot state name
    let some declaration := state.find? (·.name == name)
      | throw s!"unknown tree state '{name}'"
    let .tree schema := declaration.kind
      | throw s!"state '{name}' is not a recursive map"
    schema.removalPath keys
    let alignedKeys ← nativePathKeys keys
    plan := {plan with operations := plan.operations ++ [.mapRemove slot alignedKeys]}
  pure plan

private def previousEffectLoop (state : List StateDecl) (effects : List Effect)
    (initial : Plan) : Except String Plan := do
  let mut plan := initial
  for effect in effects do
    plan ← previousEffectStep state effect plan
  pure plan

private theorem previousEffectStep_eq_appendEffect (state : List StateDecl)
    (effect : Effect) (plan : Plan) :
    previousEffectStep state effect plan = appendEffect state effect plan := by
  cases effect <;> simp [previousEffectStep, appendEffect, stateSlot] <;> rfl

/-- Every old loop result and first failure equals the production effect
fold, for arbitrary plans, schemas, and ordered effect lists. -/
theorem previousEffectLoop_eq_appendEffect (state : List StateDecl)
    (effects : List Effect) (initial : Plan) :
    previousEffectLoop state effects initial =
      appendEffects state effects initial := by
  unfold appendEffects
  unfold previousEffectLoop
  simp only [bind_pure]
  change (forIn effects initial (fun effect plan => do
      let result ← previousEffectStep state effect plan
      pure (ForInStep.yield result))) =
    effects.foldlM (fun plan effect => appendEffect state effect plan) initial
  have stepEq (effect : Effect) (plan : Plan) :
      (do let result ← previousEffectStep state effect plan
          pure (ForInStep.yield result)) =
        ForInStep.yield <$> previousEffectStep state effect plan := by
    cases previousEffectStep state effect plan <;> rfl
  simp only [stepEq]
  rw [List.forIn_yield_eq_foldlM]
  simp only [previousEffectStep_eq_appendEffect, Except.map, Functor.map]
  congr 1
  funext plan effect
  cases appendEffect state effect plan <;> rfl

/-- Final production gate for a symbolic native plan. -/
def finishPlan (entry : Entrypoint) (result : Except String Plan) : Except Diagnostic Plan :=
  match result with
  | .ok plan =>
    match plan.validate entry with
    | .ok _ => pure plan
    | .error message => throw {span := entry.span, message}
  | .error message => throw {span := entry.span, message}

/-- Lower a typed entrypoint to a symbolic native VM program. The state layout
is a root array with one slot per declaration. Cells, including booleans, use
Native field alignment. Membership results use the VM's byte-aligned boolean.
The plan is not deployable until its fields are bound by the relation producer. -/
def lower (state : List StateDecl) (entry : Entrypoint) : Except Diagnostic Plan := do
  entry.validate ledgerCapabilities state
  Disclosure.entrypoint entry
  let result : Except String Plan := do
    let mut plan : Plan := {}
    let sourceNames := entry.circuit.inputs.map (·.name) ++ entry.circuit.outputs.map (·.name) ++
      entry.effects.flatMap (fun effect => match effect with
        | .readCell _ destination _ | .readMap _ destination .. |
            .readMember _ destination .. | .readPath _ destination .. |
            .memberPath _ destination .. | .counterRead _ destination .. |
            .listLength _ destination .. => [destination]
        | .readCompositePath _ _ _ _ destinations => destinations
        | .listHead _ _ _ _ destinations => destinations
        | _ => [])
    if sourceNames.any (·.startsWith "_noctium_") then
      throw "source names beginning '_noctium_' are reserved by the native transcript producer"
    -- Public parameters must appear among Popeq reads consumed by public_input.
    plan ← publicInputPlan entry.circuit.inputs plan
    plan ← appendEffectsGuarded state entry.effects entry.effectGuards plan
    pure plan
  finishPlan entry result

private def bytes (n : Nat) : List Nat := if n == 0 then [] else go n (n.log2 / 8 + 1)
where
  go (n : Nat) : Nat → List Nat
    | 0 => []
    | fuel + 1 => n % 256 :: go (n / 256) fuel

/-- JSON value atoms must be hydrated into Uint8Array by the ledger JS adapter. -/
def Aligned.toJson (ctx : EvalContext) (env : EvalEnv) (value : Aligned) : Except String Lean.Json := do
  let (atoms, alignment) ← match value with
    | .field expression => do
      pure (Lean.toJson [bytes (← expression.eval ctx env)],
        Lean.Json.mkObj [("tag", Lean.toJson ("field" : String))])
    | .bit b => pure (Lean.toJson [bytes (if b then 1 else 0)],
        Lean.Json.mkObj [("tag", Lean.toJson ("bytes" : String)), ("length", Lean.toJson (1 : Nat))])
    | .bitExpr expression => pure (Lean.toJson [bytes (if ← expression.eval ctx env then 1 else 0)],
        Lean.Json.mkObj [("tag", Lean.toJson ("bytes" : String)), ("length", Lean.toJson (1 : Nat))])
    | .bytes32 expression => do
      let values ← expression.eval ctx env
      pure (Lean.Json.arr #[Lean.Json.arr (values.toArray.map Lean.toJson)],
        Lean.Json.mkObj [("tag", Lean.toJson ("bytes" : String)),
          ("length", Lean.toJson (32 : Nat))])
    | .nativeFields _ => throw "grouped Native fields serialize through pushFields/popeqFields"
    | .counter expression => do
      let value ← expression.eval ctx env
      pure (Lean.toJson [bytes value], Lean.Json.mkObj [
        ("tag", Lean.toJson ("bytes" : String)), ("length", Lean.toJson (8 : Nat))])
  pure (Lean.Json.mkObj [("value", atoms),
    ("alignment", Lean.Json.arr #[Lean.Json.mkObj [
      ("tag", Lean.toJson ("atom" : String)), ("value", alignment)]])])

def Op.toJson (ctx : EvalContext) (env : EvalEnv) : Op → Except String Lean.Json
  | .dup => pure (Lean.Json.mkObj [("dup", Lean.Json.mkObj [("n", Lean.toJson (0 : Nat))])])
  | .index slot pushPath => do
    let value ← (Aligned.field (.native slot)).toJson ctx env
    pure (Lean.Json.mkObj [("idx", Lean.Json.mkObj [
      ("cached", Lean.toJson false), ("pushPath", Lean.toJson pushPath),
      ("path", Lean.Json.arr #[Lean.Json.mkObj [("tag", Lean.toJson ("value" : String)), ("value", value)]])])])
  | .mapIndex slot key => do
    let slotValue ← (Aligned.field (.native slot)).toJson ctx env
    let keyValue ← key.toJson ctx env
    pure (Lean.Json.mkObj [("idx", Lean.Json.mkObj [
      ("cached", Lean.toJson false), ("pushPath", Lean.toJson false),
      ("path", Lean.Json.arr #[
        Lean.Json.mkObj [("tag", Lean.toJson ("value" : String)), ("value", slotValue)],
        Lean.Json.mkObj [("tag", Lean.toJson ("value" : String)), ("value", keyValue)]])])])
  | .indexPath slot pushPath keys => do
    let slotValue ← (Aligned.field (.native slot)).toJson ctx env
    let keyValues ← keys.mapM fun key => key.toJson ctx env
    let path := (slotValue :: keyValues).map fun value =>
      Lean.Json.mkObj [("tag", Lean.toJson ("value" : String)), ("value", value)]
    pure (Lean.Json.mkObj [("idx", Lean.Json.mkObj [
      ("cached", Lean.toJson false), ("pushPath", Lean.toJson pushPath),
      ("path", Lean.Json.arr path.toArray)])])
  | .push value storage => do
    pure (Lean.Json.mkObj [("push", Lean.Json.mkObj [("storage", Lean.toJson storage),
      ("value", Lean.Json.mkObj [("tag", Lean.toJson ("cell" : String)),
        ("content", ← value.toJson ctx env)])])])
  | .newMap => pure (Lean.Json.mkObj [("new", Lean.Json.mkObj [])])
  | .popeq value => do
    pure (Lean.Json.mkObj [("popeq", Lean.Json.mkObj [("cached", Lean.toJson false),
      ("result", ← value.toJson ctx env)])])
  | .pushFields schema values storage => do
    let values ← values.mapM (fun value => value.eval ctx env)
    pure (Lean.Json.mkObj [("pushFields", Lean.Json.mkObj [
      ("schema", schema), ("storage", Lean.toJson storage), ("values", Lean.toJson values)])])
  | .popeqFields schema values => do
    let values ← values.mapM (fun value => value.eval ctx env)
    pure (Lean.Json.mkObj [("popeqFields", Lean.Json.mkObj [
      ("schema", schema), ("values", Lean.toJson values)])])
  | .member => pure (Lean.toJson ("member" : String))
  | .insert levels => pure (Lean.Json.mkObj [("ins", Lean.Json.mkObj [
      ("cached", Lean.toJson false), ("n", Lean.toJson levels)])])
  | .addImmediate amount => pure (Lean.Json.mkObj [("addi", Lean.Json.mkObj [
      ("immediate", Lean.toJson amount)])])
  | .subImmediate amount => pure (Lean.Json.mkObj [("subi", Lean.Json.mkObj [
      ("immediate", Lean.toJson amount)])])
  | .listLength slot keys value => do
    pure (Lean.Json.mkObj [("listLength", Lean.Json.mkObj [
      ("slot", Lean.toJson slot), ("keyCount", Lean.toJson keys.length),
      ("value", Lean.toJson (← value.eval ctx env))])])
  | .listHead slot keys schema values => do
    let values ← values.mapM (fun value => value.eval ctx env)
    pure (Lean.Json.mkObj [("listHead", Lean.Json.mkObj [
      ("slot", Lean.toJson slot), ("keyCount", Lean.toJson keys.length),
      ("schema", schema), ("values", Lean.toJson values)])])
  | .listPushFront slot keys schema values => do
    let values ← values.mapM (fun value => value.eval ctx env)
    pure (Lean.Json.mkObj [("listPushFront", Lean.Json.mkObj [
      ("slot", Lean.toJson slot), ("keyCount", Lean.toJson keys.length),
      ("schema", schema), ("values", Lean.toJson values)])])
  | .listPopFront slot keys => pure (Lean.Json.mkObj [("listPopFront", Lean.Json.mkObj [
      ("slot", Lean.toJson slot), ("keyCount", Lean.toJson keys.length)])])
  | .listReset slot keys => pure (Lean.Json.mkObj [("listReset", Lean.Json.mkObj [
      ("slot", Lean.toJson slot), ("keyCount", Lean.toJson keys.length)])])
  | .mapRemove slot keys => pure (Lean.Json.mkObj [("mapRemove", Lean.Json.mkObj [
      ("slot", Lean.toJson slot), ("keyCount", Lean.toJson keys.length)])])

def Plan.toJson (ctx : EvalContext) (env : EvalEnv) (plan : Plan) : Except String Lean.Json := do
  pure (Lean.Json.arr (← plan.operations.mapM (Op.toJson ctx env)).toArray)

end Noctium.Backend.Impact
