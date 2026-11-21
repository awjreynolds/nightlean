import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Types

private def mixedFabEnvironment : CompositeEnv := {
  enumerations := [{id := "MixedFabPersistentHash.LeafMarker", variants := [
    {name := "Only"}
  ]}],
  structures := [{id := "MixedFabPersistentHash.FabPayload", fields := [
    {name := "octets", type := .bytes 32},
    {name := "flag", type := .scalar .bool},
    {name := "counter", type := .scalar (.uint 65535)},
    {name := "marker", type := .enumeration "MixedFabPersistentHash.LeafMarker"},
    {name := "anchor", type := .scalar .native}
  ]}]
}

private def mixedFabPayloadType : CompositeType :=
  .structure "MixedFabPersistentHash.FabPayload"

noctium_circuit mixedFabPersistentHashInputs where
  private octets : Bytes32
  private flag : Bool
  private counterInput : UInt 16
  private anchor : Native
  output digest : Bytes32 := disclose(persistentHashFab(
    mixedFabEnvironment, mixedFabPayloadType, [octets, flag, counterInput, uint(0), anchor]))
end

noctium_contract MixedFabPersistentHash where
  entry hash uses mixedFabPersistentHashInputs where
    return resultHash : Bytes32 := digest
  end
end

private def mixedFabEntry : Entrypoint :=
  match MixedFabPersistentHash.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Native.expectedEntrypoint MixedFabPersistentHash.state mixedFabEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint MixedFabPersistentHash.state mixedFabEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

/-- undisclosed private parameter 'octets' -/
#guard_msgs (substring := true) in
noctium_circuit mixedFabUndisclosed where
  private octets : Bytes32
  private flag : Bool
  private counterInput : UInt 16
  private anchor : Native
  output digest : Bytes32 := persistentHashFab(
    mixedFabEnvironment, mixedFabPayloadType, [octets, flag, counterInput, uint(0), anchor])
end
