import Nightlean.Backend.Impact
import Nightlean.Claim
import Nightlean.Backend.Zkir

open Nightlean
open Nightlean.Backend.Impact

def main (args : List String) : IO Unit := do
  let ctx : EvalContext := {
    modulus := Field.modulus
    poseidon2 := fun _ _ _ => .error "transcript planner must not invoke a hash oracle" }
  let env : EvalEnv := [("root", .native 99), ("campaign", .native 7),
    ("suppliedNullifier", .native 123), ("nullifier", .native 123),
    ("storedRoot", .native 99), ("storedCampaign", .native 7)]
  let contract ← match Claim.contract with
    | .ok c => pure c
    | .error e => throw (IO.userError e)
  let some entry := contract.entrypoints.head? | throw (IO.userError "missing claim entrypoint")
  let plan ← match lower contract.state entry with
    | .ok p => pure p
    | .error d => throw (IO.userError d.message)
  unless plan.reads.length == 6 && plan.guards.length == 3 do
    throw (IO.userError "transcript read/guard count mismatch")
  if args == ["--zkir"] then
    match Nightlean.Backend.Zkir.lowerEntrypoint contract.state entry with
    | .error d => throw (IO.userError d.message)
    | .ok json => IO.println json.compress
    return
  let ops ← match plan.toJson ctx env with
    | .ok json => pure json
    | .error e => throw (IO.userError e)
  IO.println ops.compress
