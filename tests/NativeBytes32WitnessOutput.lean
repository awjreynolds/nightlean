import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_witness_circuit accountHash where
  private accountSecret : Bytes32
  public expectedAccountId : Bytes32
  prove eq(expectedAccountId, persistentHash32(accountSecret))
  output accountId : Bytes32 := disclose(persistentHash32(accountSecret))
end

noctium_contract NativeBytes32WitnessOutput where
  map registered : Bytes32 => Bool
  entry register uses accountHash where
    insert registered[disclose(accountId)] := true
    member registered[disclose(accountId)] as found
    require eq(found, true)
  end
end

private def nativeBytes32OutputEntry : Entrypoint :=
  match NativeBytes32WitnessOutput.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Disclosure.circuit {
    name := "unreleasedBytes32Output"
    inputs := [{name := "accountSecret", ty := .bytes 32, visibility := .private}]
    outputs := [{name := "accountId", ty := .bytes 32, value := .persistentHash32 (.ref "accountSecret")}]
  } with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

#guard match Backend.Zkir.lowerEntrypoint
    NativeBytes32WitnessOutput.state nativeBytes32OutputEntry with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false
