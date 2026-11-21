import Noctium.Frontend

open scoped Noctium

noctium_circuit foreignKeys where
  public owner : Native
  public baseKey : Secp256k1Base
  public scalarKey : Curve25519Scalar
  public pointKey : Curve25519Point
  public secpKey : Secp256k1Point
  public amount : UInt 64
  public leafHash : Bytes32
  public removing : Bool
end

noctium_contract ForeignKeys where
  map baseValues : Secp256k1Base => UInt 64
  map scalarValues : Curve25519Scalar => UInt 64
  map pointValues : Curve25519Point => UInt 64
  map secpValues : Secp256k1Point => UInt 64
  set registeredPoints : Curve25519Point
  tree nestedScalars : Native => Curve25519Scalar => UInt 64
  tree pointGroups : Native => Set Curve25519Point
  tree claimTrees : Secp256k1Point => MerkleTree 2
  constructor() where
  end
  entry update uses foreignKeys where
    member baseValues[disclose(baseKey)] as basePresent
    when eq(basePresent, true) read baseValues[disclose(baseKey)] as baseBefore
    when eq(removing, false) insert baseValues[disclose(baseKey)] := disclose(amount)
    when removing remove baseValues[disclose(baseKey)]
    member baseValues[disclose(baseKey)] as baseAfter
    when eq(baseAfter, true) read baseValues[disclose(baseKey)] as baseAfterValue

    member scalarValues[disclose(scalarKey)] as directScalarPresent
    when eq(removing, false) insert scalarValues[disclose(scalarKey)] := disclose(amount)
    when removing remove scalarValues[disclose(scalarKey)]
    member scalarValues[disclose(scalarKey)] as directScalarAfter

    member pointValues[disclose(pointKey)] as pointMapPresent
    when eq(removing, false) insert pointValues[disclose(pointKey)] := disclose(amount)
    when removing remove pointValues[disclose(pointKey)]
    member pointValues[disclose(pointKey)] as pointMapAfter

    member secpValues[disclose(secpKey)] as secpMapPresent
    when eq(removing, false) insert secpValues[disclose(secpKey)] := disclose(amount)
    when removing remove secpValues[disclose(secpKey)]
    member secpValues[disclose(secpKey)] as secpMapAfter

    member registeredPoints[disclose(pointKey)] as pointPresent
    when eq(removing, false) insert registeredPoints[disclose(pointKey)]
    when removing remove registeredPoints[disclose(pointKey)]
    member registeredPoints[disclose(pointKey)] as pointAfter

    member nestedScalars[disclose(owner)] as scalarOwnerPresent
    if eq(scalarOwnerPresent, false) then {
      insert nestedScalars[disclose(owner)] := emptyMap
    } else {
    }
    member nestedScalars[disclose(owner)][disclose(scalarKey)] as scalarPresent
    insert nestedScalars[disclose(owner)][disclose(scalarKey)] := disclose(amount)
    when removing remove nestedScalars[disclose(owner)][disclose(scalarKey)]
    member nestedScalars[disclose(owner)][disclose(scalarKey)] as scalarAfter

    member pointGroups[disclose(owner)] as pointGroupPresent
    when eq(pointGroupPresent, false) reset pointGroups[disclose(owner)]
    member pointGroups[disclose(owner)][disclose(pointKey)] as groupedPointPresent
    when eq(removing, false) insert pointGroups[disclose(owner)][disclose(pointKey)]
    when removing remove pointGroups[disclose(owner)][disclose(pointKey)]
    member pointGroups[disclose(owner)][disclose(pointKey)] as groupedPointAfter

    member claimTrees[disclose(secpKey)] as claimTreePresent
    when eq(claimTreePresent, false) reset claimTrees[disclose(secpKey)]
    insertHash claimTrees[disclose(secpKey)] := disclose(leafHash)

    return baseBeforeValue : UInt 64 := disclose(baseBefore)
    return baseValue : UInt 64 := disclose(baseAfterValue)
    return baseExisted : Bool := basePresent
    return baseExists : Bool := baseAfter
    return scalarMapExisted : Bool := directScalarPresent
    return scalarMapExists : Bool := directScalarAfter
    return pointMapExisted : Bool := pointMapPresent
    return pointMapExists : Bool := pointMapAfter
    return secpMapExisted : Bool := secpMapPresent
    return secpMapExists : Bool := secpMapAfter
    return pointExisted : Bool := pointPresent
    return pointExists : Bool := pointAfter
    return scalarExisted : Bool := scalarPresent
    return scalarExists : Bool := scalarAfter
    return groupedPointExisted : Bool := groupedPointPresent
    return groupedPointExists : Bool := groupedPointAfter
  end
end
