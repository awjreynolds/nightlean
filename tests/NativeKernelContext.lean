import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit kernelContextInputs where
  public enabled : Bool
  public color : Bytes32
  public isUnshielded : Bool
end

noctium_contract NativeKernelContext where
  entry inspect uses kernelContextInputs where
    when enabled readSelf as own
    when enabled readCaller as (present, isContract, contractId, userId)
    when enabled tokenBalance(color, isUnshielded) as amount
    return selfAddress : Bytes32 := own
    return hasCaller : Bool := present
    return contractCaller : Bool := isContract
    return callerContract : Bytes32 := contractId
    return callerUser : Bytes32 := userId
    return tokenBalance : UInt 128 := amount
  end
end

private def kernelContextArgs (enabled isUnshielded : _root_.Bool)
    (color : List Nat) : EvalEnv := [
  ("enabled", .bool enabled),
  ("color", .bytes 32 color),
  ("isUnshielded", .bool isUnshielded)
]

private def kernelContextRun (context : EvalContext) (args : EvalEnv) :=
  match NativeKernelContext.entrypoints with
  | ep :: _ => ep.run context args {}
  | [] => Except.error "missing kernel-context entrypoint"

#guard
  let own := List.range 32
  let caller := List.replicate 32 99
  let color := List.range 32
  let context : EvalContext := {
    modulus := Field.modulus,
    poseidon2 := fun _ _ _ => .error "unused",
    ownContractAddress := some own,
    caller := some (.contract caller),
    unshieldedBalances := [(color, 17)],
    shieldedBalances := [(color, 23)]
  }
  match kernelContextRun context (kernelContextArgs Bool.true Bool.true color) with
  | .ok (outputs, state) => outputs == [
      ("selfAddress", .bytes 32 own),
      ("hasCaller", .bool Bool.true),
      ("contractCaller", .bool Bool.true),
      ("callerContract", .bytes 32 caller),
      ("callerUser", .bytes 32 (List.replicate 32 0)),
      ("tokenBalance", .uint balanceMaximum 17)
    ] && state == {}
  | .error _ => Bool.false

#guard
  let own := List.range 32
  let caller := List.replicate 32 99
  let color := List.range 32
  let context : EvalContext := {
    modulus := Field.modulus,
    poseidon2 := fun _ _ _ => .error "unused",
    ownContractAddress := some own,
    caller := some (.user caller),
    unshieldedBalances := [(color, 17)],
    shieldedBalances := [(color, 23)]
  }
  match kernelContextRun context (kernelContextArgs Bool.true Bool.false color) with
  | .ok (outputs, state) => outputs == [
      ("selfAddress", .bytes 32 own),
      ("hasCaller", .bool Bool.true),
      ("contractCaller", .bool Bool.false),
      ("callerContract", .bytes 32 (List.replicate 32 0)),
      ("callerUser", .bytes 32 caller),
      ("tokenBalance", .uint balanceMaximum 23)
    ] && state == {}
  | .error _ => Bool.false

#guard
  let context : EvalContext := {
    modulus := Field.modulus,
    poseidon2 := fun _ _ _ => .error "unused",
    caller := some (.contract (List.replicate 32 99))
  }
  let color := List.range 32
  match kernelContextRun context (kernelContextArgs Bool.false Bool.true color) with
  | .ok (outputs, state) => outputs == [
      ("selfAddress", .bytes 32 (List.replicate 32 0)),
      ("hasCaller", .bool Bool.false),
      ("contractCaller", .bool Bool.false),
      ("callerContract", .bytes 32 (List.replicate 32 0)),
      ("callerUser", .bytes 32 (List.replicate 32 0)),
      ("tokenBalance", .uint balanceMaximum 0)
    ] && state == {}
  | .error _ => Bool.false

#guard
  let context : EvalContext := {
    modulus := Field.modulus,
    poseidon2 := fun _ _ _ => .error "unused",
    ownContractAddress := some (List.replicate 32 256),
    caller := some (.contract (List.replicate 32 99))
  }
  let color := List.range 32
  match kernelContextRun context (kernelContextArgs Bool.true Bool.true color) with
  | .error "invalid execution contract address" => Bool.true
  | _ => Bool.false

#guard
  let own := List.range 32
  let context : EvalContext := {
    modulus := Field.modulus,
    poseidon2 := fun _ _ _ => .error "unused",
    ownContractAddress := some own,
    caller := some (.user (List.replicate 32 256))
  }
  let color := List.range 32
  match kernelContextRun context (kernelContextArgs Bool.true Bool.true color) with
  | .error "invalid caller address" => Bool.true
  | _ => Bool.false

#guard
  match NativeKernelContext.entrypoints with
  | [entrypoint] =>
      (Backend.Native.expectedEntrypoint NativeKernelContext.state entrypoint).isOk &&
        (Backend.Zkir.lowerEntrypoint NativeKernelContext.state entrypoint).isOk
  | _ => Bool.false
