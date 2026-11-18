import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Types.Composite

open scoped Noctium
open Noctium

noctium_circuit foreignTreeValues where
  public owner : Native
  public domain : Bytes32
  private scalar : Curve25519Scalar
  private curvePoint : Curve25519Point
  private secpPoint : Secp256k1Point
end

noctium_contract ForeignTree where
  tree scalars : Native => Bytes32 => Curve25519Scalar
  tree curvePoints : Bytes32 => Native => Curve25519Point
  tree secpPoints : Bytes32 => Bytes32 => Secp256k1Point
  constructor() where
  end
  entry update uses foreignTreeValues where
    member scalars[disclose(owner)] as scalarOwnerPresent
    if eq(scalarOwnerPresent, false) then {
      insert scalars[disclose(owner)] := emptyMap
    } else {
    }
    member scalars[disclose(owner)][disclose(domain)] as scalarLeafPresent
    when eq(scalarLeafPresent, true) read scalars[disclose(owner)][disclose(domain)] as scalarBeforeRead
    insert scalars[disclose(owner)][disclose(domain)] := disclose(scalar)
    read scalars[disclose(owner)][disclose(domain)] as scalarAfterRead

    member curvePoints[disclose(domain)] as curvePointDomainPresent
    if eq(curvePointDomainPresent, false) then {
      insert curvePoints[disclose(domain)] := emptyMap
    } else {
    }
    member curvePoints[disclose(domain)][disclose(owner)] as curvePointLeafPresent
    when eq(curvePointLeafPresent, true) read curvePoints[disclose(domain)][disclose(owner)] as curvePointBeforeRead
    insert curvePoints[disclose(domain)][disclose(owner)] := disclose(curvePoint)
    read curvePoints[disclose(domain)][disclose(owner)] as curvePointAfterRead

    member secpPoints[disclose(domain)] as secpPointDomainPresent
    if eq(secpPointDomainPresent, false) then {
      insert secpPoints[disclose(domain)] := emptyMap
    } else {
    }
    member secpPoints[disclose(domain)][bytes32("point")] as secpPointLeafPresent
    when eq(secpPointLeafPresent, true) read secpPoints[disclose(domain)][bytes32("point")] as secpPointBeforeRead
    insert secpPoints[disclose(domain)][bytes32("point")] := disclose(secpPoint)
    read secpPoints[disclose(domain)][bytes32("point")] as secpPointAfterRead

    return oldScalar : Curve25519Scalar := disclose(scalarBeforeRead)
    return oldCurvePoint : Curve25519Point := disclose(curvePointBeforeRead)
    return oldSecpPoint : Secp256k1Point := disclose(secpPointBeforeRead)
    return newScalar : Curve25519Scalar := disclose(scalarAfterRead)
    return newCurvePoint : Curve25519Point := disclose(curvePointAfterRead)
    return newSecpPoint : Secp256k1Point := disclose(secpPointAfterRead)
  end
end

private def foreignTreeEntry : Entrypoint :=
  match ForeignTree.entrypoints with
  | ep :: _ => ep
  | _ => {name := "missing", circuit := {name := "missing"}}

#guard match ForeignTree.validate Capabilities.source with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Impact.lower ForeignTree.state foreignTreeEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

#guard match Backend.Zkir.lowerEntrypoint ForeignTree.state foreignTreeEntry with
  | .ok _ => Bool.true
  | .error _ => Bool.false

private def foreignTreeRecordEnvironment : Types.CompositeEnv := {
  structures := [{
    id := "ForeignTree.ForeignRecord"
    fields := [⟨"value", .scalar (.foreign (.scalar .curve25519)), {}⟩]
  }]
}

#guard match (LedgerValueType.composite foreignTreeRecordEnvironment
    (.structure "ForeignTree.ForeignRecord")).validate Capabilities.source with
  | .error _ => Bool.true
  | .ok _ => Bool.false
