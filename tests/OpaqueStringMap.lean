import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit opaqueStringStoreInputs where
  public key : Bytes32
  public value : OpaqueString
end

noctium_circuit opaqueStringReadInputs where
  public key : Bytes32
end

noctium_contract OpaqueStringMap where
  tree strings : Bytes32 => OpaqueString
  entry store uses opaqueStringStoreInputs where
    insert strings[disclose(key)] := disclose(value)
  end
  entry «read» uses opaqueStringReadInputs where
    read strings[disclose(key)] as storedValue
    return value : OpaqueString := disclose(storedValue)
  end
end

private def opaqueStringStoreEntry : Entrypoint :=
  match OpaqueStringMap.entrypoints.find? (·.name == "store") with
  | some value => value
  | none => {name := "missing", circuit := {name := "missing"}}

private def opaqueStringReadEntry : Entrypoint :=
  match OpaqueStringMap.entrypoints.find? (·.name == "read") with
  | some value => value
  | none => {name := "missing", circuit := {name := "missing"}}

#guard match OpaqueStringMap.state with
  | [{name := "strings", kind := .tree (.map (.bytes 32) (.scalar .opaqueString)), ..}] => Bool.true
  | _ => Bool.false

#guard match OpaqueStringMap.validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match ({name := "MutableOpaqueStringCell", state := [
    {name := "value", kind := .cell .opaqueString}]} : Contract).validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard ([StateKind.map (.bytes 32) .opaqueString,
    .tree (.map .native (.map (.bytes 32) (.scalar .opaqueString)))]).all fun kind =>
  let unsupported : Contract := {name := "Unsupported", state := [{name := "strings", kind}]}
  match unsupported.validate Capabilities.source with
  | .error diagnostic => diagnostic.message.contains "root Bytes32 tree Map value"
  | .ok _ => Bool.false

#guard match Backend.Impact.lower OpaqueStringMap.state opaqueStringStoreEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower OpaqueStringMap.state opaqueStringReadEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint OpaqueStringMap.state opaqueStringStoreEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerPrunedEntrypoint OpaqueStringMap.state opaqueStringReadEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false
