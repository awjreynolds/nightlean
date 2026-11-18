import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit jubjubStorageValues where
  public owner : Native
  public domain : Bytes32
  private scalar : JubjubScalar
  private point : JubjubPoint
end

noctium_contract JubjubStorage where
  cell scalarCell : JubjubScalar
  cell pointCell : JubjubPoint
  map scalarMap : Native => JubjubScalar
  map pointMap : Bytes32 => JubjubPoint
  tree scalars : Native => Bytes32 => JubjubScalar
  tree points : Bytes32 => Native => JubjubPoint
  constructor() where
    initialize scalarCell := jubjubScalarFromNative(0)
    initialize pointCell := jubjubFromCoordinates(0, 1)
  end
  entry update uses jubjubStorageValues where
    read scalarCell as initialScalarCell
    read pointCell as initialPointCell

    member scalarMap[disclose(owner)] as scalarMapExists
    when eq(scalarMapExists, true)
      read scalarMap[disclose(owner)] as previousScalarMap
    member pointMap[disclose(domain)] as pointMapExists
    when eq(pointMapExists, true)
      read pointMap[disclose(domain)] as previousPointMap

    member scalars[disclose(owner)] as scalarOwnerExists
    if eq(scalarOwnerExists, false) then {
      insert scalars[disclose(owner)] := emptyMap
    } else {
    }
    member scalars[disclose(owner)][disclose(domain)] as scalarTreeExists
    when eq(scalarTreeExists, true)
      read scalars[disclose(owner)][disclose(domain)] as previousScalarTree

    member points[disclose(domain)] as pointDomainExists
    if eq(pointDomainExists, false) then {
      insert points[disclose(domain)] := emptyMap
    } else {
    }
    member points[disclose(domain)][disclose(owner)] as pointTreeExists
    when eq(pointTreeExists, true)
      read points[disclose(domain)][disclose(owner)] as previousPointTree

    write scalarCell := disclose(scalar)
    write pointCell := disclose(point)
    insert scalarMap[disclose(owner)] := disclose(scalar)
    insert pointMap[disclose(domain)] := disclose(point)
    insert scalars[disclose(owner)][disclose(domain)] := disclose(scalar)
    insert points[disclose(domain)][disclose(owner)] := disclose(point)

    read scalarCell as nextScalarCell
    read pointCell as nextPointCell
    read scalarMap[disclose(owner)] as nextScalarMap
    read pointMap[disclose(domain)] as nextPointMap
    read scalars[disclose(owner)][disclose(domain)] as nextScalarTree
    read points[disclose(domain)][disclose(owner)] as nextPointTree

    return oldScalarCell : JubjubScalar := disclose(initialScalarCell)
    return oldPointCell : JubjubPoint := disclose(initialPointCell)
    return oldScalarMap : JubjubScalar := disclose(previousScalarMap)
    return oldPointMap : JubjubPoint := disclose(previousPointMap)
    return oldScalarTree : JubjubScalar := disclose(previousScalarTree)
    return oldPointTree : JubjubPoint := disclose(previousPointTree)
    return newScalarCell : JubjubScalar := disclose(nextScalarCell)
    return newPointCell : JubjubPoint := disclose(nextPointCell)
    return newScalarMap : JubjubScalar := disclose(nextScalarMap)
    return newPointMap : JubjubPoint := disclose(nextPointMap)
    return newScalarTree : JubjubScalar := disclose(nextScalarTree)
    return newPointTree : JubjubPoint := disclose(nextPointTree)
  end
end

private def jubjubStorageEntry : Entrypoint :=
  match JubjubStorage.entrypoints with
  | entrypoint :: _ => entrypoint
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match JubjubStorage.validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match JubjubStorage.validate {Capabilities.source with jubjub := _root_.Bool.false} with
  | .error _ => Bool.true
  | .ok _ => Bool.false

#guard match ({name := "jubjubCell", state := [
    {name := "value", kind := .cell .jubjubScalar}]} : Contract).validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match ({name := "unqualifiedJubjubCell", state := [
    {name := "value", kind := .cell .jubjubScalar}]} : Contract).validate
    {Capabilities.source with jubjub := _root_.Bool.false} with
  | .error diagnostic => diagnostic.message == "target lacks qualified Jubjub support"
  | .ok _ => Bool.false

#guard match ({name := "jubjubMap", state := [
    {name := "values", kind := .map (.bytes 32) .jubjubPoint}]} : Contract).validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match ({name := "unqualifiedJubjubMap", state := [
    {name := "values", kind := .map (.bytes 32) .jubjubPoint}]} : Contract).validate
    {Capabilities.source with jubjub := _root_.Bool.false} with
  | .error diagnostic => diagnostic.message == "target lacks qualified Jubjub support"
  | .ok _ => Bool.false

#guard match (LedgerValueType.map .native (.scalar .jubjubScalar)).validate
    {Capabilities.source with jubjub := _root_.Bool.false} with
  | .error "target lacks qualified Jubjub support" => Bool.true
  | .ok _ | .error _ => Bool.false

#guard match (LedgerValueType.map .native (.scalar .jubjubScalar)).validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard jubjubStorageEntry.returns.map Output.name == [
  "oldScalarCell", "oldPointCell", "oldScalarMap", "oldPointMap", "oldScalarTree", "oldPointTree",
  "newScalarCell", "newPointCell", "newScalarMap", "newPointMap", "newScalarTree", "newPointTree"]

#guard match Backend.Impact.lower JubjubStorage.state jubjubStorageEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint JubjubStorage.state jubjubStorageEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def jubjubStorageUndisclosedWrite : Entrypoint := {
  name := "jubjubStorageUndisclosedWrite"
  circuit := jubjubStorageValues
  effects := [.writeCell "scalarCell" .jubjubScalar (.ref "scalar")]
}

#guard match Disclosure.entrypoint jubjubStorageUndisclosedWrite with
  | .error _ => Bool.true
  | .ok _ => Bool.false
