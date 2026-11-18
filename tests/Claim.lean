import Noctium.Claim

open Noctium

private def caps : Capabilities := {poseidon2 := true, stateCells := true, stateMaps := true}

#guard match Claim.contract {} with
  | .ok c => match c.validate caps with | .ok _ => true | _ => false
  | _ => false
#guard match Claim.relation {depth := 4} with
  | .ok c => c.inputs.length == 4 + 4 * 2
  | _ => false
#guard match Claim.relation {depth := 0} with | .error _ => true | _ => false
#guard match Claim.relation {depth := 9} with | .error _ => true | _ => false
#guard match ({leaf := 1, node := 1, nullifier := 3} : Claim.Domains).validate with
  | .error _ => true | _ => false
#guard match ({leaf := Field.modulus} : Claim.Domains).validate with
  | .error _ => true | _ => false
#guard match Claim.initialState Field.modulus 1 with | .error _ => true | _ => false

-- Policy-only tests deliberately omit cryptography. They exercise state guards,
-- not eligibility or proof validity. The cryptographic relation fails without
-- an independently qualified Poseidon implementation.
private def ctx : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "no qualified hash oracle in policy test"
}
private def env : EvalEnv := [("root", .native 7), ("campaign", .native 8), ("nullifier", .native 9)]
private def policy : Except String (List Effect) := do
  let c ← Claim.contract {}
  match c.entrypoints with
  | [e] => pure e.effects
  | _ => throw "invalid claim builder"

#guard match policy, Claim.initialState 7 8 with
  | .ok effects, .ok state => match runEffects ctx effects env state with
    | .ok next => match runEffects ctx effects env next with | .error _ => true | _ => false
    | _ => false
  | _, _ => false
#guard match policy, Claim.initialState 6 8 with
  | .ok effects, .ok state => match runEffects ctx effects env state with
    | .error _ => true | _ => false
  | _, _ => false
#guard match policy, Claim.initialState 7 6 with
  | .ok effects, .ok state => match runEffects ctx effects env state with
    | .error _ => true | _ => false
  | _, _ => false
#guard match Claim.relation {} with
  | .ok c => match c.run ctx [
      ("root", .native 7), ("campaign", .native 8), ("suppliedNullifier", .native 9),
      ("secret", .native 10), ("sibling0", .native 11), ("sibling1", .native 12),
      ("direction0", .bool false), ("direction1", .bool true)] with
    | .error "no qualified hash oracle in policy test" => true
    | _ => false
  | _ => false
