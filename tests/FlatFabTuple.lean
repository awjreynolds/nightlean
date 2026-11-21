import Noctium.Frontend
import Noctium.Backend.NativeExpected
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium
open Noctium.Types

private def flatFabTupleEnvironment : CompositeEnv := {
  enumerations := [{id := "FlatFabTuple.LeafMarker", variants := [
    {name := "Only"}
  ]}]
}

private def flatFabTupleType : CompositeType := .tuple [
  .bytes 32,
  .scalar .bool,
  .scalar (.uint 65535),
  .enumeration "FlatFabTuple.LeafMarker",
  .scalar .native
]

noctium_circuit flatFabTupleInputs where
  private octets : Bytes32
  private flag : Bool
  private counterInput : UInt 16
  private persistentOpening : Bytes32
  private transientOpening : Native
  private anchor : Native
  output hashDigest : Bytes32 := disclose(persistentHashFab(
    flatFabTupleEnvironment, flatFabTupleType, [octets, flag, counterInput, uint(0), anchor]))
  output persistentCommitment : Bytes32 := disclose(persistentCommitFab(
    flatFabTupleEnvironment, flatFabTupleType, persistentOpening,
    [octets, flag, counterInput, uint(0), anchor]))
  output transientCommitment : Native := disclose(transientCommitFab(
    flatFabTupleEnvironment, flatFabTupleType, transientOpening,
    [octets, flag, counterInput, uint(0), anchor]))
end

noctium_contract FlatFabTuple where
  entry hash uses flatFabTupleInputs where
    return hashResult : Bytes32 := hashDigest
    return persistentResult : Bytes32 := persistentCommitment
    return transientResult : Native := transientCommitment
  end
end

private def flatFabTupleEntry : Entrypoint :=
  match FlatFabTuple.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match Backend.Native.expectedEntrypoint FlatFabTuple.state flatFabTupleEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint FlatFabTuple.state flatFabTupleEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false
