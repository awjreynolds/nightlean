import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit lazyBooleanInputs where
  private andEnabled : Bool
  private orEnabled : Bool
  private nestedOuter : Bool
  private nestedInner : Bool
  private amount : UInt 8
  output andValue : Bool := disclose(andThen(andEnabled,
    eq(cast(UInt 1, amount), uint(1))))
  output orValue : Bool := disclose(orElse(orEnabled,
    eq(cast(UInt 1, amount), uint(1))))
  output nestedValue : Bool := disclose(andThen(nestedOuter,
    orElse(nestedInner, eq(cast(UInt 1, amount), uint(1)))))
end

noctium_contract LazyBoolean where
  entry lazy uses lazyBooleanInputs where
    return andResult : Bool := disclose(andValue)
    return orResult : Bool := disclose(orValue)
    return nestedResult : Bool := disclose(nestedValue)
  end
end

private def lazyBooleanEvalContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => pure 0
}

private def lazyBooleanEnv (andEnabled orEnabled nestedOuter nestedInner : _root_.Bool) : EvalEnv := [
  ("andEnabled", .bool andEnabled),
  ("orEnabled", .bool orEnabled),
  ("nestedOuter", .bool nestedOuter),
  ("nestedInner", .bool nestedInner),
  ("amount", .uint 255 2)]

private def evalLazyBooleanOutputs (env : EvalEnv) :
    Except String (_root_.Bool × _root_.Bool × _root_.Bool) := do
  match lazyBooleanInputs.outputs with
  | [⟨_, .bool, andExpr, _⟩, ⟨_, .bool, orExpr, _⟩, ⟨_, .bool, nestedExpr, _⟩] => do
    let andValue ← andExpr.eval lazyBooleanEvalContext env
    let orValue ← orExpr.eval lazyBooleanEvalContext env
    let nestedValue ← nestedExpr.eval lazyBooleanEvalContext env
    pure (andValue, orValue, nestedValue)
  | _ => throw "lazy Boolean fixture output shape changed"

#guard match evalLazyBooleanOutputs (lazyBooleanEnv Bool.false Bool.true Bool.false Bool.false) with
  | .ok (Bool.false, Bool.true, Bool.false) => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match evalLazyBooleanOutputs (lazyBooleanEnv Bool.true Bool.true Bool.false Bool.false) with
  | .error _ => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match evalLazyBooleanOutputs (lazyBooleanEnv Bool.false Bool.false Bool.false Bool.false) with
  | .error _ => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match evalLazyBooleanOutputs (lazyBooleanEnv Bool.false Bool.true Bool.true Bool.false) with
  | .error _ => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match evalLazyBooleanOutputs (lazyBooleanEnv Bool.false Bool.true Bool.true Bool.true) with
  | .ok (Bool.false, Bool.true, Bool.true) => _root_.Bool.true
  | _ => _root_.Bool.false
