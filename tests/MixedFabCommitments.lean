import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Types

private def mixedFabCommitmentsEnvironment : CompositeEnv := {
  enumerations := [{id := "MixedFabCommitments.LeafMarker", variants := [
    {name := "Only"}
  ]}],
  structures := [{id := "MixedFabCommitments.FabPayload", fields := [
    {name := "octets", type := .bytes 32},
    {name := "flag", type := .scalar .bool},
    {name := "counter", type := .scalar (.uint 65535)},
    {name := "marker", type := .enumeration "MixedFabCommitments.LeafMarker"},
    {name := "anchor", type := .scalar .native}
  ]}]
}

private def mixedFabCommitmentsPayloadType : CompositeType :=
  .structure "MixedFabCommitments.FabPayload"

noctium_circuit mixedFabCommitmentsInputs where
  private octets : Bytes32
  private flag : Bool
  private counterInput : UInt 16
  private persistentOpening : Bytes32
  private transientOpening : Native
  private anchor : Native
  output persistentCommitment : Bytes32 := disclose(persistentCommitFab(
    mixedFabCommitmentsEnvironment, mixedFabCommitmentsPayloadType, persistentOpening,
    [octets, flag, counterInput, uint(0), anchor]))
  output transientCommitment : Native := disclose(transientCommitFab(
    mixedFabCommitmentsEnvironment, mixedFabCommitmentsPayloadType, transientOpening,
    [octets, flag, counterInput, uint(0), anchor]))
end

noctium_contract MixedFabCommitments where
  entry commit uses mixedFabCommitmentsInputs where
    return persistentResult : Bytes32 := persistentCommitment
    return transientResult : Native := transientCommitment
  end
end

private def mixedFabCommitmentsEntry : Entrypoint :=
  match MixedFabCommitments.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Native.expectedEntrypoint MixedFabCommitments.state mixedFabCommitmentsEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint MixedFabCommitments.state mixedFabCommitmentsEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false
