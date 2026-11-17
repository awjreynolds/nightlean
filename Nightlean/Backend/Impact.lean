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
  | mapIndex (slot : Nat) (key : Scalar)
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
  | .mapIndex slot key => [.native 0x51] ++
      (Aligned.field (.native slot)).fields ++ (Aligned.field key).fields
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
  /-- Optional source activity guard per opcode group. Empty means all groups
  are active, preserving historical plans. -/
  activityGuards : List (Option (Expr .bool)) := []
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
  unless plan.activityGuards.isEmpty || plan.activityGuards.length == plan.operations.length do
    throw "native activity guard schedule length mismatch"
  for guard in plan.activityGuards do
    if let some guard := guard then guard.validate {poseidon2 := true} env

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

/-- One effect in the production ordered ledger plan. The current read count
fixes generated absence names and therefore belongs to the accumulator. -/
def appendEffect (state : List StateDecl) (effect : Effect)
    (plan : Plan) : Except String Plan := do
  match effect with
  | .readCell name destination ty =>
    let slot ← stateSlot state name
    pure { plan with
      operations := plan.operations ++ [.dup, .index slot, .popeq (.field (nativeRead ty destination))]
      reads := plan.reads ++ [{name := destination, ty}] }
  | .require condition =>
    pure {plan with guards := plan.guards ++ [condition]}
  | .requireAbsent name _ key =>
    let slot ← stateSlot state name
    let readName := s!"_nightlean_absence_{plan.reads.length}"
    pure { plan with
      operations := plan.operations ++ [
        .dup, .index slot, .push (.field (nativeValue _ key)), .member, .popeq (.bit false)]
      reads := plan.reads ++ [{name := readName, ty := .bool}]
      guards := plan.guards ++ [.eq (.ref readName : Expr .bool) (.bool false)] }
  | .writeCell name _ value =>
    let slot ← stateSlot state name
    pure {plan with operations := plan.operations ++ [
      .push (.field (.native slot)), .push (.field (nativeValue _ value)) true, .insert 1]}
  | .writeMap name _ _ key value =>
    let slot ← stateSlot state name
    pure {plan with operations := plan.operations ++ [
      .index slot true, .push (.field (nativeValue _ key)),
      .push (.field (nativeValue _ value)) true, .insert 2]}
  | .readMap name destination _ ty key => do
    let slot ← stateSlot state name
    pure { plan with
      operations := plan.operations ++ [
        .dup, .mapIndex slot (nativeValue _ key),
        .popeq (.field (nativeRead ty destination))]
      reads := plan.reads ++ [{name := destination, ty}] }

def appendEffects (state : List StateDecl) (effects : List Effect)
    (initial : Plan) : Except String Plan :=
  effects.foldlM (fun plan effect => appendEffect state effect plan) initial

/-- Lower one source effect and bind its generated opcode groups to the exact
source activity guard. Operations before the first guard retain implicit true. -/
private def appendEffectWithActivity (state : List StateDecl) (effect : Effect)
    (guard : Option (Expr .bool)) (plan : Plan) : Except String Plan := do
  let before := plan.operations.length
  let result ← appendEffect state effect plan
  let added := result.operations.length - before
  if guard.isSome && added == 0 then
    throw "native guards are supported only on cell and map writes"
  if guard.isNone && plan.activityGuards.isEmpty then
    pure result
  else
    let priorGuards := if plan.activityGuards.isEmpty then List.replicate before none
      else plan.activityGuards
    pure {result with activityGuards := priorGuards ++ List.replicate added guard}

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

private def appendPublicInput (input : Input) (plan : Plan) : Plan :=
  if input.visibility == .«public» then
    let value := Aligned.field (nativeRead input.ty input.name)
    { plan with
      operations := plan.operations ++ [.push value, .popeq value]
      reads := plan.reads ++ [{name := input.name, ty := input.ty}] }
  else plan

/-- The exact public-input prefix used before source effects. -/
def publicInputPlan (inputs : List Input) (initial : Plan := {}) : Plan :=
  inputs.foldl (fun plan input => appendPublicInput input plan) initial

private def previousPublicInputStep (input : Input) (plan : Plan) : Plan :=
  if input.visibility == .«public» then
    let value := Aligned.field (nativeRead input.ty input.name)
    { plan with
        operations := plan.operations ++ [.push value, .popeq value]
        reads := plan.reads ++ [{name := input.name, ty := input.ty}] }
  else plan

private def previousPublicInputLoop (inputs : List Input) (initial : Plan) : Except String Plan := do
  let mut plan := initial
  for input in inputs do
    plan := previousPublicInputStep input plan
  pure plan

/-- The old mutable public-input loop equals the production pure prefix for
all input lists and starting plans. -/
theorem previousPublicInputLoop_eq_publicInputPlan (inputs : List Input)
    (initial : Plan) :
    previousPublicInputLoop inputs initial = .ok (publicInputPlan inputs initial) := by
  unfold previousPublicInputLoop
  simp only [bind_pure]
  change (forIn inputs initial (fun input plan =>
      (pure (ForInStep.yield (previousPublicInputStep input plan)) : Except String (ForInStep Plan)))) =
    .ok (publicInputPlan inputs initial)
  rw [List.forIn_pure_yield_eq_foldl]
  rfl

/-- Imperative counterpart retained for the kernel equivalence check. -/
private def previousEffectStep (state : List StateDecl) (effect : Effect)
    (initial : Plan) : Except String Plan := do
  let mut plan := initial
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
    plan := {plan with operations := plan.operations ++ [
      .push (.field (.native slot)), .push (.field (nativeValue _ value)) true, .insert 1]}
  | .writeMap name _ _ key value =>
    let slot ← stateSlot state name
    plan := {plan with operations := plan.operations ++ [
      .index slot true, .push (.field (nativeValue _ key)),
      .push (.field (nativeValue _ value)) true, .insert 2]}
  | .readMap name destination _ ty key => do
    let slot ← stateSlot state name
    plan := { plan with
      operations := plan.operations ++ [
        .dup, .mapIndex slot (nativeValue _ key),
        .popeq (.field (nativeRead ty destination))]
      reads := plan.reads ++ [{name := destination, ty}] }
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
    plan := publicInputPlan entry.circuit.inputs plan
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
  | .mapIndex slot key => do
    let slotValue ← (Aligned.field (.native slot)).toJson ctx env
    let keyValue ← (Aligned.field key).toJson ctx env
    pure (Lean.Json.mkObj [("idx", Lean.Json.mkObj [
      ("cached", Lean.toJson false), ("pushPath", Lean.toJson false),
      ("path", Lean.Json.arr #[
        Lean.Json.mkObj [("tag", Lean.toJson ("value" : String)), ("value", slotValue)],
        Lean.Json.mkObj [("tag", Lean.toJson ("value" : String)), ("value", keyValue)]])])])
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
