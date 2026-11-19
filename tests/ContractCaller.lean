import Noctium.Frontend

open scoped Noctium

noctium_circuit protectedInput where
  private amount : Native
end

noctium_contract ProtectedCallee where
  cell permitted : Bytes32
  cell enforce : Bool
  cell balance : Native
  entry move uses protectedInput arguments [amount] where
    read permitted as parent
    read enforce as checkCaller
    when checkCaller requireContractCaller(parent)
    read balance as previous
    write balance := disclose(add(previous, amount))
    return result : Native := disclose(add(previous, amount))
  end
end

noctium_circuit forwardingInput where
  public target : Bytes32
  private opening : Native
  private amount : Native
  private expected : Native
end

noctium_contract ForwardingCaller where
  cell marker : Native
  entry forward uses forwardingInput where
    claimContractCall(target,
      disclose(callCommitment(ProtectedCallee, "move", opening, [amount], [expected])))
  end
end

private def protectedEntry : Noctium.Entrypoint :=
  match ProtectedCallee.entrypoints with
  | value :: _ => value
  | [] => {name := "missing", circuit := {name := "missing"}}

#guard !(Noctium.Disclosure.entrypoint {protectedEntry with
  circuit := {protectedEntry.circuit with inputs := protectedEntry.circuit.inputs ++
    [{name := "secretAddress", ty := .bytes 32, visibility := .private}]},
  effects := protectedEntry.effects.map fun effect => match effect with
    | .requireContractCaller _ => .requireContractCaller (.ref "secretAddress")
    | _ => effect}).isOk
