import Nightlean.IR
import Nightlean.Field
import Nightlean.Semantics
import Nightlean.Disclosure

namespace Nightlean.Backend.Impact

/-- Symbols in the ledger public-input sequence are source expressions, not
free transcript values. Each symbol must be computed or publicly read by ZKIR. -/
abbrev Scalar := Expr .native

inductive Aligned where
  | field (value : Scalar)
  | bit (value : Bool)
  deriving Repr

inductive Op where
  | dup
  | index (slot : Nat) (pushPath : Bool := false)
  | push (value : Aligned) (storage : Bool := false)
  | popeq (value : Aligned)
  | member
  | insert (levels : Nat)
  deriving Repr

/-- Field-representation vectors match ledger-9 onchain-vm/src/ops.rs and
transient-crypto/src/fab.rs. Index keys use Native field alignment. -/
def Aligned.fields : Aligned → List Scalar
  | .field value => [.native 1, .native (Field.modulus - 2), value]
  | .bit value => [.native 1, .native 1, .native (if value then 1 else 0)]

def Op.fields : Op → List Scalar
  | .dup => [.native 0x30]
  | .index slot pushPath => [.native (if pushPath then 0x70 else 0x50)] ++
      (Aligned.field (.native slot)).fields
  | .push value storage => [.native (if storage then 0x11 else 0x10), .native 1] ++ value.fields
  | .popeq value => [.native 0x0c] ++ value.fields
  | .member => [.native 0x18]
  | .insert levels => [.native (0x90 + levels)]

structure Read where
  name : String
  ty : Ty
  deriving Repr

structure Plan where
  operations : List Op := []
  reads : List Read := []
  guards : List (Expr .bool) := []
  deriving Repr

def Plan.fields (plan : Plan) : List Scalar := plan.operations.flatMap Op.fields

/-- Generated field expressions must retain the source/read types even though
their native representation is uniformly a field. -/
def Plan.validate (plan : Plan) (entry : Entrypoint) : Except String Unit := do
  let publicCount := (entry.circuit.inputs.filter (·.visibility == .«public»)).length
  let env := entry.circuit.inputs.map (fun input => (input.name, input.ty)) ++
    entry.circuit.outputs.map (fun output => (output.name, output.ty)) ++
    (plan.reads.drop publicCount).map (fun read => (read.name, read.ty))
  for field in plan.fields do field.validate {poseidon2 := true} env
  for guard in plan.guards do guard.validate {poseidon2 := true} env

private def nativeValue : (ty : Ty) → Expr ty → Scalar
  | .native, value => value
  | .bool, value => .select value (.native 1) (.native 0)
  | .uint _, value => .cast .native value

private def nativeRead (ty : Ty) (name : String) : Scalar :=
  match ty with
  | .native => .ref name
  | .bool => .cast .native (.ref name : Expr .bool)
  | .uint maximum => .cast .native (.ref name : Expr (.uint maximum))

private def stateSlot (state : List StateDecl) (name : String) : Except String Nat :=
  match state.findIdx? (·.name == name) with
  | some index => pure index
  | none => throw s!"unknown ledger state '{name}'"

/-- Lower a typed entrypoint to a symbolic native VM program. The state layout
is a root array with one slot per declaration. Cells, including booleans, use
Native field alignment. Membership results use the VM's byte-aligned boolean.
The plan is not deployable until its fields are bound by the relation producer. -/
def lower (state : List StateDecl) (entry : Entrypoint) : Except Diagnostic Plan := do
  entry.validate {poseidon2 := true, stateCells := true, stateMaps := true} state
  Disclosure.entrypoint entry
  let result : Except String Plan := do
    let mut plan : Plan := {}
    let sourceNames := entry.circuit.inputs.map (·.name) ++ entry.circuit.outputs.map (·.name) ++
      entry.effects.filterMap (fun effect => match effect with
        | .readCell _ destination _ | .readMap _ destination .. => some destination
        | _ => none)
    if sourceNames.any (·.startsWith "_nightlean_") then
      throw "source names beginning '_nightlean_' are reserved by the native transcript producer"
    -- Public parameters must appear among Popeq reads consumed by public_input.
    for input in entry.circuit.inputs do
      if input.visibility == .«public» then
        let value := Aligned.field (nativeRead input.ty input.name)
        plan := { plan with
          operations := plan.operations ++ [.push value, .popeq value]
          reads := plan.reads ++ [{name := input.name, ty := input.ty}] }
    for effect in entry.effects do
      match effect with
      | .readCell name destination ty =>
        let slot ← stateSlot state name
        plan := { plan with
          operations := plan.operations ++ [.dup, .index slot, .popeq (.field (nativeRead ty destination))]
          reads := plan.reads ++ [{name := destination, ty}] }
      | .require condition =>
        plan := {plan with guards := plan.guards ++ [condition]}
      | .requireAbsent name _ key =>
        let slot ← stateSlot state name
        let name := s!"_nightlean_absence_{plan.reads.length}"
        plan := { plan with
          operations := plan.operations ++ [
            .dup, .index slot, .push (.field (nativeValue _ key)), .member, .popeq (.bit false)]
          reads := plan.reads ++ [{name, ty := .bool}]
          guards := plan.guards ++ [.eq (.ref name : Expr .bool) (.bool false)] }
      | .writeCell name _ value =>
        let slot ← stateSlot state name
        -- Preserve the root container and the slot path for ins 1.
        plan := {plan with operations := plan.operations ++ [
          .push (.field (.native slot)), .push (.field (nativeValue _ value)) true, .insert 1]}
      | .writeMap name _ _ key value =>
        let slot ← stateSlot state name
        -- idxp leaves root, slot, map; ins 2 updates map then root.
        plan := {plan with operations := plan.operations ++ [
          .index slot true, .push (.field (nativeValue _ key)),
          .push (.field (nativeValue _ value)) true, .insert 2]}
      | .readMap .. => throw "map value reads are not supported by the initial native transcript plan"
    pure plan
  match result with
  | .ok plan =>
    match plan.validate entry with
    | .ok _ => pure plan
    | .error message => throw {span := entry.span, message}
  | .error message => throw {span := entry.span, message}

private def bytes (n : Nat) : List Nat := if n == 0 then [] else go n (n.log2 / 8 + 1)
where
  go (n : Nat) : Nat → List Nat
    | 0 => []
    | fuel + 1 => n % 256 :: go (n / 256) fuel

/-- JSON value atoms must be hydrated into Uint8Array by the ledger JS adapter. -/
def Aligned.toJson (ctx : EvalContext) (env : EvalEnv) (value : Aligned) : Except String Lean.Json := do
  let (number, alignment) ← match value with
    | .field expression => do pure (← expression.eval ctx env,
        Lean.Json.mkObj [("tag", Lean.toJson ("field" : String))])
    | .bit b => pure ((if b then 1 else 0),
        Lean.Json.mkObj [("tag", Lean.toJson ("bytes" : String)), ("length", Lean.toJson (1 : Nat))])
  pure (Lean.Json.mkObj [("value", Lean.toJson [bytes number]),
    ("alignment", Lean.Json.arr #[Lean.Json.mkObj [
      ("tag", Lean.toJson ("atom" : String)), ("value", alignment)]])])

def Op.toJson (ctx : EvalContext) (env : EvalEnv) : Op → Except String Lean.Json
  | .dup => pure (Lean.Json.mkObj [("dup", Lean.Json.mkObj [("n", Lean.toJson (0 : Nat))])])
  | .index slot pushPath => do
    let value ← (Aligned.field (.native slot)).toJson ctx env
    pure (Lean.Json.mkObj [("idx", Lean.Json.mkObj [
      ("cached", Lean.toJson false), ("pushPath", Lean.toJson pushPath),
      ("path", Lean.Json.arr #[Lean.Json.mkObj [("tag", Lean.toJson ("value" : String)), ("value", value)]])])])
  | .push value storage => do
    pure (Lean.Json.mkObj [("push", Lean.Json.mkObj [("storage", Lean.toJson storage),
      ("value", Lean.Json.mkObj [("tag", Lean.toJson ("cell" : String)),
        ("content", ← value.toJson ctx env)])])])
  | .popeq value => do
    pure (Lean.Json.mkObj [("popeq", Lean.Json.mkObj [("cached", Lean.toJson false),
      ("result", ← value.toJson ctx env)])])
  | .member => pure (Lean.toJson ("member" : String))
  | .insert levels => pure (Lean.Json.mkObj [("ins", Lean.Json.mkObj [
      ("cached", Lean.toJson false), ("n", Lean.toJson levels)])])

def Plan.toJson (ctx : EvalContext) (env : EvalEnv) (plan : Plan) : Except String Lean.Json := do
  pure (Lean.Json.arr (← plan.operations.mapM (Op.toJson ctx env)).toArray)

end Nightlean.Backend.Impact
