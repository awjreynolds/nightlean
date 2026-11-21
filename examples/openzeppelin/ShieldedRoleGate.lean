import Noctium.Frontend

/-!
One protected action using the role-membership slice of the pinned OpenZeppelin
ShieldedAccessControl source (`f85f1a23685c6bbedfc8c2589ae3aa128aff7c46`, blob
`68cee5368e49951c62dcaa40fa75e8c3d3d023bc`). The upstream contract file is
OpenZeppelin Compact Contracts v0.5.0-alpha.2 and requires language 0.28.0 or
later. Its fixture compiler pin is Compact 0.36.1, language 0.28.0.

The Noctium witness ABI carries the depth-20 path as a checked named structure:
Bytes32 commitment leaf, then 20 entries of Field sibling plus direction Bool.
The circuit authorizes the private direction bits to control the disclosed
root calculation. The contract checks the computed root and revocation
nullifier before incrementing protectedActions.
-/
open scoped Noctium
open Noctium

namespace OpenZeppelinPort.ShieldedRoleGate

private def rolePathWire : Helpers.Wire.Codec := {
  payload := .structure "ShieldedRolePath"
  frameBytes := 692
  composites := {
    structures := [
      {id := "MerkleTreeDigest", fields := [
        {name := "field", type := .scalar .native}
      ]},
      {id := "MerkleTreePathEntry", fields := [
        {name := "sibling", type := .structure "MerkleTreeDigest"},
        {name := "goes_left", type := .scalar .bool}
      ]},
      {id := "ShieldedRolePath", fields := [
        {name := "leaf", type := .bytes 32},
        {name := "path", type := .vector 20 (.structure "MerkleTreePathEntry")}
      ]}
    ]
  }
}

private def roleLeafWire : Helpers.Wire.Codec := {
  payload := .bytes 32
  frameBytes := 32
}

noctium_witness shieldedSecret() : Bytes32
noctium_witness roleCommitmentPath(commitment : Bytes32) : Payload rolePathWire

noctium_witness_circuit shieldedRoleGate using rolePathWire, roleLeafWire where
  public role : Bytes32
  public instanceSalt : Bytes32
  let secret := witness shieldedSecret()
  let accountId := persistentHashVector32([
    secret,
    instanceSalt,
    bytes32("ShieldedAccessControl:accountId")
  ])
  let roleCommitment := persistentHashVector32([
    role,
    accountId,
    instanceSalt,
    bytes32("ShieldedAccessControl:commitment")
  ])
  let path := witness roleCommitmentPath(roleCommitment)
  let encodedLeaf := encode(roleLeafWire, field(path, leaf))
  prove eq(encodedLeaf, roleCommitment)
  let leafPreimage := concatBytes(bytes(6, "mdn:lh"), encodedLeaf)
  let leafDigest := sha256(leafPreimage)
  let leafField := degradeToNative(leafDigest)
  let currentRoot := fold(leafField, [field(path, path)], fun current step =>
    let sibling := field(field(step, sibling), field) in
    let goesLeft := disclose(field(step, goes_left)) in
    transientHashNativeVector([
      select(goesLeft, current, sibling),
      select(goesLeft, sibling, current)
    ])
  )
  let roleNullifier := persistentHashVector32([
    roleCommitment,
    bytes32("ShieldedAccessControl:nullifier")
  ])
  output candidateRoot : Native := disclose(currentRoot)
  output nullifier : Bytes32 := disclose(roleNullifier)
end

noctium_contract ShieldedRoleGate where
  sealed cell instanceSalt : Bytes32
  merkleTree operatorRoles : 20 of Bytes32
  set revokedRoleNullifiers : Bytes32
  counter protectedActions

  constructor(instanceSalt : Bytes32) where
    initialize instanceSalt := instanceSalt
  end

  entry protectedAction uses shieldedRoleGate where
    read instanceSalt as configuredSalt
    require eq(configuredSalt, instanceSalt)
    checkRoot operatorRoles against disclose(candidateRoot) as rootMatches
    member revokedRoleNullifiers[disclose(nullifier)] as isRevoked
    require eq(rootMatches, true)
    require eq(isRevoked, false)
    increment protectedActions by 1
  end
end

end OpenZeppelinPort.ShieldedRoleGate
