import Noctium.Types.Values

namespace Noctium.Types

abbrev SomeTypedValue := (type : CompiledType) × TypedValue type

inductive Projection where
  | tupleIndex (index : Nat)
  | field (name : String)
  | vectorIndex (index : Nat)
  | byteIndex (index : Nat)
  | enumField (variant name : String)
  deriving Repr, BEq

private def makeChild (parent : CompiledType) (type : CompositeType) (value : AggregateValue) :
    Except String SomeTypedValue := do
  let child ← (compileType parent.environment type parent.limits).mapError (·.message)
  pure ⟨child, ← checkValue child value⟩

def project (parent : CompiledType) (value : TypedValue parent) (projection : Projection) :
    Except String SomeTypedValue := do
  match parent.type, value.value, projection with
  | .tuple types, .tuple values, .tupleIndex index =>
    let some type := types[index]? | throw "aggregate tuple projection out of bounds"
    let some value := values[index]? | throw "aggregate tuple value projection out of bounds"
    makeChild parent type value
  | .structure id, .structure _ values, .field name =>
    let some declaration := parent.environment.structures.find? (·.id == id) | throw "unknown aggregate struct"
    let some field := declaration.fields.find? (·.name == name) | throw "unknown aggregate struct field"
    let some value := values.lookup name | throw "missing aggregate struct value field"
    makeChild parent field.type value
  | .vector length type, .vector values, .vectorIndex index =>
    unless index < length do throw "aggregate vector index out of bounds"
    let some value := values[index]? | throw "aggregate vector value index out of bounds"
    makeChild parent type value
  | .bytes length, .bytes values, .byteIndex index =>
    unless index < length do throw "aggregate byte index out of bounds"
    let some value := values[index]? | throw "aggregate byte value index out of bounds"
    makeChild parent (.scalar (.uint 255)) (.scalar (.uint 255) value)
  | .enumeration id, .enumeration _ active values, .enumField variant name =>
    unless variant == active do throw "aggregate enum pattern does not match active variant"
    let some declaration := parent.environment.enumerations.find? (·.id == id) | throw "unknown aggregate enum"
    let some selected := declaration.variants.find? (·.name == variant) | throw "unknown aggregate enum variant"
    let some field := selected.fields.find? (·.name == name) | throw "unknown aggregate enum field"
    let some value := values.lookup name | throw "missing aggregate enum value field"
    makeChild parent field.type value
  | _, _, _ => throw "aggregate projection kind/type mismatch"

def decompose (parent : CompiledType) (value : TypedValue parent) :
    Except String (List (String × SomeTypedValue)) := do
  match parent.type, value.value with
  | .unit, .unit => pure []
  | .tuple types, .tuple _ =>
    (List.range types.length).mapM fun index => do
      pure (toString index, ← project parent value (.tupleIndex index))
  | .structure _, .structure _ fields =>
    fields.mapM fun (name, _) => do pure (name, ← project parent value (.field name))
  | .enumeration _, .enumeration _ variant fields =>
    fields.mapM fun (name, _) => do pure (name, ← project parent value (.enumField variant name))
  | .vector length _, .vector _ =>
    (List.range length).mapM fun index => do
      pure (toString index, ← project parent value (.vectorIndex index))
  | .bytes length, .bytes _ =>
    (List.range length).mapM fun index => do
      pure (toString index, ← project parent value (.byteIndex index))
  | _, _ => throw "aggregate scalar has no aggregate pattern components"

/-- The index's origins remain separate even when the selected component is unit
or has no scalar leaves. This is bookkeeping, not a disclosure authorization. -/
structure Selection where
  value : SomeTypedValue
  componentOrigins : List Disclosure.Origins
  indexOrigins : Disclosure.Origins
  variantOrigins : Disclosure.Origins
  controlOrigins : Disclosure.Origins := []

structure TrackedValue (type : CompiledType) where
  value : TypedValue type
  componentOrigins : List Disclosure.Origins
  count : componentOrigins.length = type.checked.expandedLeaves

def trackValue (type : CompiledType) (value : TypedValue type) (origins : List Disclosure.Origins) :
    Except String (TrackedValue type) :=
  if count : origins.length = type.checked.expandedLeaves then
    .ok {value, componentOrigins := origins, count}
  else .error "aggregate component origin count mismatch"

private def layoutSlice (layout : Layout) (projection : Projection) : Except String (Nat × Nat × Bool) := do
  match layout, projection with
  | .tuple items, .tupleIndex index =>
    let some selected := items[index]? | throw "aggregate tuple layout index out of bounds"
    pure ((items.take index).map Layout.leafCount |>.sum, selected.leafCount, false)
  | .structure _ fields, .field name =>
    let some index := fields.findIdx? (·.1 == name) | throw "unknown aggregate layout field"
    let some selected := fields[index]? | throw "aggregate field layout index mismatch"
    pure ((fields.take index).map (fun field => field.2.leafCount) |>.sum, selected.2.leafCount, false)
  | .vector length element, .vectorIndex index =>
    unless index < length do throw "aggregate vector layout index out of bounds"
    pure (index * element.leafCount, element.leafCount, false)
  | .bytes length _, .byteIndex index =>
    unless index < length do throw "aggregate byte layout index out of bounds"
    pure (index, 1, false)
  | .enumeration _ _ _ _ _ variants, .enumField variant name =>
    let some selected := variants.find? (·.1 == variant) | throw "unknown aggregate layout variant"
    let some index := selected.2.1.findIdx? (·.1 == name) | throw "unknown aggregate variant layout field"
    let some field := selected.2.1[index]? | throw "aggregate variant layout index mismatch"
    pure (1 + ((selected.2.1.take index).map (fun item => item.2.leafCount)).sum, field.2.leafCount, true)
  | _, _ => throw "aggregate projection layout mismatch"

def projectTracked (parent : CompiledType) (value : TrackedValue parent) (projection : Projection)
    (indexOrigins : Disclosure.Origins := []) (controlOrigins : Disclosure.Origins := []) : Except String Selection := do
  let selected ← project parent value.value projection
  let (offset, count, variantSelected) ← layoutSlice parent.checked.value projection
  let origins := (value.componentOrigins.drop offset).take count
  unless origins.length == selected.1.checked.expandedLeaves do throw "aggregate origin slice count mismatch"
  pure {
    value := selected
    componentOrigins := origins
    indexOrigins := indexOrigins
    controlOrigins := controlOrigins
    variantOrigins := if variantSelected then value.componentOrigins.headD [] else []
  }

def Selection.conservativeOrigins (value : Selection) : List Disclosure.Origins :=
  value.componentOrigins.map fun origins =>
    (origins ++ value.indexOrigins ++ value.variantOrigins ++ value.controlOrigins).eraseDups

theorem tracked_leaf_origin_count (type : CompiledType) (value : TrackedValue type) :
    value.componentOrigins.length = type.checked.value.leafCount := by
  rw [type.checked.leafCountMatches]
  exact value.count

end Noctium.Types
