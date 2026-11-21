import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit receiveInputs where
  public color : Bytes32
  public amount : UInt 128
  public enabled : Bool
end

noctium_contract ReceiveUnshielded where
  entry receive uses receiveInputs where
    when enabled receiveUnshielded(color, amount)
  end
  entry primitive uses receiveInputs where
    when enabled incUnshieldedInputs(color, amount, true)
  end
end

private def receiveEntry (name : String) : Entrypoint :=
  match ReceiveUnshielded.entrypoints.find? (·.name == name) with
  | some candidate => candidate
  | none => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Zkir.lowerPrunedEntrypoint ReceiveUnshielded.state
    (receiveEntry "receive") with
  | .ok (_, helperRelation) =>
    match Backend.Zkir.lowerPrunedEntrypoint ReceiveUnshielded.state
        (receiveEntry "primitive") with
    | .ok (_, primitiveRelation) => helperRelation == primitiveRelation
    | .error _ => Bool.false
  | .error _ => Bool.false
