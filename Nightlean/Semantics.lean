import Nightlean.Disclosure

namespace Nightlean

abbrev Ty.Denote : Ty → Type
  | .native => Nat
  | .bool => Bool
  | .uint _ => Nat

inductive Value where
  | native (value : Nat)
  | bool (value : Bool)
  | uint (maximum value : Nat)
  deriving Repr, BEq, DecidableEq

def Value.as : (ty : Ty) → Value → Option ty.Denote
  | .native, .native n => some n
  | .bool, .bool b => some b
  | .uint maximum, .uint found n => if maximum == found then some n else none
  | _, _ => none

def Value.pack : (ty : Ty) → ty.Denote → Value
  | .native, n => .native n
  | .bool, b => .bool b
  | .uint maximum, n => .uint maximum n

abbrev EvalEnv := List (String × Value)

/-- The hash oracle must be the qualified target implementation. No placeholder
hash is supplied by the reference semantics. -/
structure EvalContext where
  modulus : Nat
  poseidon2 : Nat → Nat → Nat → Except String Nat

private def sameValue : (ty : Ty) → ty.Denote → ty.Denote → Bool
  | .native, a, b => a == b
  | .bool, a, b => a == b
  | .uint _, a, b => a == b

private def canonical (ctx : EvalContext) (ty : Ty) (v : ty.Denote) : Bool :=
  match ty with
  | .native => v < ctx.modulus
  | .bool => true
  | .uint maximum => maximum ≤ ScalarPolicy.maxUint && v ≤ maximum && v < ctx.modulus

private def scalarNumber : (ty : Ty) → ty.Denote → Nat
  | .native, n | .uint _, n => n
  | .bool, b => if b then 1 else 0

private def scalarCast (ctx : EvalContext) (target : Ty) (number : Nat) : Except String target.Denote :=
  match target with
  | .native => if number < ctx.modulus then pure number else .error "noncanonical scalar conversion"
  | .bool => pure (number != 0)
  | .uint maximum =>
    if maximum ≤ ScalarPolicy.maxUint && number ≤ maximum && number < ctx.modulus then pure number
    else .error "scalar conversion exceeds unsigned bound"

/-- Evaluation is total and returns errors for absent/mistyped witnesses or
noncanonical field data, rather than silently inventing witness values. -/
def Expr.eval (ctx : EvalContext) (env : EvalEnv) : Expr ty → Except String ty.Denote
  | .native n => if n < ctx.modulus then pure n else .error "noncanonical native constant"
  | .bool b => .ok b
  | .uint maximum n =>
    if canonical ctx (.uint maximum) n then pure n else .error "noncanonical unsigned constant"
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
    scalarCast ctx target (scalarNumber source (← value.eval ctx env))
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
    (Expr.disclose span value).eval ctx env = value.eval ctx env := by rfl

def Circuit.run (ctx : EvalContext) (c : Circuit) (env : EvalEnv) : Except String EvalEnv := do
  match c.validate {nativeModulus := ctx.modulus, poseidon2 := true} with
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
  deriving Repr, BEq

private def updateAssoc [BEq α] (key : α) (value : β) (entries : List (α × β)) : List (α × β) :=
  (key, value) :: entries.filter (fun item => !(item.1 == key))

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
  pure next

/-- This is a specification evaluator, not a substitute for ledger proof checks. -/
def Entrypoint.run (ctx : EvalContext) (entry : Entrypoint) (env : EvalEnv)
    (state : LedgerState) : Except String (EvalEnv × LedgerState) := do
  match Disclosure.entrypoint entry with
  | .error diagnostic => throw diagnostic.message
  | .ok _ => pure ()
  let outputs ← entry.circuit.run ctx env
  let next ← runEffects ctx entry.effects (outputs ++ env) state
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
