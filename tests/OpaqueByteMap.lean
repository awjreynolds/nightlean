import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit opaqueByteStoreInputs where
  public key : Bytes32
  public payload : OpaqueBytes
end

noctium_circuit opaqueByteReadInputs where
  public key : Bytes32
end

noctium_contract OpaqueByteMap where
  tree payloads : Bytes32 => OpaqueBytes
  entry store uses opaqueByteStoreInputs where
    insert payloads[disclose(key)] := disclose(payload)
  end
  entry «read» uses opaqueByteReadInputs where
    read payloads[disclose(key)] as storedPayload
    return payload : OpaqueBytes := disclose(storedPayload)
  end
end

private def opaqueByteStoreEntry : Entrypoint :=
  match OpaqueByteMap.entrypoints.find? (·.name == "store") with
  | some value => value
  | none => {name := "missing", circuit := {name := "missing"}}

private def opaqueByteReadEntry : Entrypoint :=
  match OpaqueByteMap.entrypoints.find? (·.name == "read") with
  | some value => value
  | none => {name := "missing", circuit := {name := "missing"}}

#guard match OpaqueByteMap.state with
  | [{name := "payloads", kind := .tree (.map (.bytes 32) (.scalar .opaqueBytes)), ..}] => Bool.true
  | _ => Bool.false

#guard match OpaqueByteMap.validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower OpaqueByteMap.state opaqueByteStoreEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower OpaqueByteMap.state opaqueByteReadEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint OpaqueByteMap.state opaqueByteStoreEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint OpaqueByteMap.state opaqueByteReadEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false
