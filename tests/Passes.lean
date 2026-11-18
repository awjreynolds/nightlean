import Noctium.Passes

open Noctium
open Noctium.Passes

private def ctx : EvalContext := {
  modulus := 17
  poseidon2 := fun _ _ _ => .error "no qualified hash oracle"
}
private def fixture : Circuit := {
  name := "pass"
  inputs := [⟨"x", .native, .«public», {}⟩]
  constraints := [.bool true, .eq (.ref "x" : Expr .native) (.native 3), .bool true]
  outputs := [⟨"y", .native, .add (.ref "x") (.native 2), {}⟩]
}
#guard (pruneCircuit fixture).constraints.length == 1
#guard match (pruneCircuit fixture).run ctx [("x", .native 3)] with
  | .ok [("y", .native 5)] => true
  | _ => false
#guard (pruneCircuit {fixture with constraints := [.bool true, .bool true]}).constraints.isEmpty
#guard match (pruneCircuit {fixture with constraints := []}).run ctx [("x", .native 3)] with
  | .ok [("y", .native 5)] => true
  | _ => false
-- Invalid inputs fail before constraints in both original and optimized IR.
#guard match (pruneCircuit fixture).run ctx [] with
  | .error "missing input 'x'" => true
  | _ => false
-- Optimization retains validation failures in syntactically later constraints.
#guard match (pruneCircuit {fixture with constraints := [.bool true,
    .eq (.ref "unknown" : Expr .native) (.native 1)]}).run ctx [("x", .native 3)] with
  | .error "unknown reference 'unknown'" => true
  | _ => false
-- Literal false still stops evaluation before a subsequent fallible hash.
#guard match (pruneCircuit {fixture with constraints := [.bool true, .bool false,
    .eq (.poseidon2 1 (.native 2) (.native 3)) (.native 4)]}).run ctx [("x", .native 3)] with
  | .error "circuit constraint failed" => true
  | _ => false
-- An otherwise-reached hash failure is preserved, never optimized into success.
#guard match (pruneCircuit {fixture with constraints := [.bool true,
    .eq (.poseidon2 1 (.native 2) (.native 3)) (.native 4)]}).run ctx [("x", .native 3)] with
  | .error "no qualified hash oracle" => true
  | _ => false
-- Theorems quantify over arbitrary contexts, including failing hash oracles.
example (ctx : EvalContext) (env : EvalEnv) (c : Circuit) :
    (pruneCircuit c).run ctx env = c.run ctx env := pruneCircuit_run ctx env c
example (ctx : EvalContext) (env : EvalEnv) (s : LedgerState) (e : Entrypoint) :
    (pruneEntrypoint e).run ctx env s = e.run ctx env s := pruneEntrypoint_run ctx env s e
