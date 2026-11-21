import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit lazyConditionalInputs where
  private thenCondition : Bool
  private elseCondition : Bool
  private amount : UInt 8
  output thenValue : Bool := disclose(ite(thenCondition,
    eq(cast(UInt 1, amount), uint(1)), true))
  output elseValue : Bool := disclose(ite(elseCondition,
    true, eq(cast(UInt 1, amount), uint(1))))
end

noctium_contract LazyConditional where
  entry branches uses lazyConditionalInputs where
    return thenResult : Bool := disclose(thenValue)
    return elseResult : Bool := disclose(elseValue)
  end
end

private def lazyConditionalEvalContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => pure 0
}

private def lazyConditionalEnv (thenCondition elseCondition : _root_.Bool) : EvalEnv := [
  ("thenCondition", .bool thenCondition),
  ("elseCondition", .bool elseCondition),
  ("amount", .uint 255 2)]

private def evalLazyConditionalOutputs (env : EvalEnv) :
    Except String (_root_.Bool × _root_.Bool) := do
  match lazyConditionalInputs.outputs with
  | [⟨_, .bool, thenExpr, _⟩, ⟨_, .bool, elseExpr, _⟩] => do
    let thenValue ← thenExpr.eval lazyConditionalEvalContext env
    let elseValue ← elseExpr.eval lazyConditionalEvalContext env
    pure (thenValue, elseValue)
  | _ => throw "lazy conditional fixture output shape changed"

#guard match evalLazyConditionalOutputs (lazyConditionalEnv Bool.false Bool.true) with
  | .ok (Bool.true, Bool.true) => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match evalLazyConditionalOutputs (lazyConditionalEnv Bool.true Bool.true) with
  | .error _ => _root_.Bool.true
  | _ => _root_.Bool.false

#guard match evalLazyConditionalOutputs (lazyConditionalEnv Bool.false Bool.false) with
  | .error _ => _root_.Bool.true
  | _ => _root_.Bool.false

/-- error: Noctium expression type mismatch -/
#guard_msgs in
noctium_circuit invalidLazyConditionalTypes where
  output result : Bool := ite(false, true, uint(1))
end
