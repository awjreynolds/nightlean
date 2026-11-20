import Noctium.Frontend

open scoped Noctium

noctium_circuit nestedMerklePath where
  private owner : Bytes32
  private bucket : Native
end

noctium_circuit nestedMerkleWrite where
  private owner : Bytes32
  private bucket : Native
  private leafHash : Bytes32
  private leaf : Native
end

noctium_circuit nestedMerkleIndexed where
  private owner : Bytes32
  private bucket : Native
  private leafHash : Bytes32
  private leaf : Native
  private position : UInt 64
end

noctium_circuit nestedMerkleQuery where
  private owner : Bytes32
  private bucket : Native
  private digest : Native
end

noctium_contract NativeNestedMerkle where
  tree ordinary : Bytes32 => Native => MerkleTree 2
  tree archives : Bytes32 => Native => HistoricMerkleTree 2

  entry setup uses nestedMerklePath where
    member ordinary[disclose(owner)] as ordinaryExists
    member archives[disclose(owner)] as archiveExists
    if eq(ordinaryExists, false) then {
      insert ordinary[disclose(owner)] := emptyMap
    } else {
    }
    if eq(archiveExists, false) then {
      insert archives[disclose(owner)] := emptyMap
    } else {
    }
    reset ordinary[disclose(owner)][disclose(bucket)]
    reset archives[disclose(owner)][disclose(bucket)]
  end

  entry setupAndAppend uses nestedMerkleWrite where
    member ordinary[disclose(owner)] as ordinaryExists
    member archives[disclose(owner)] as archiveExists
    if eq(ordinaryExists, false) then {
      insert ordinary[disclose(owner)] := emptyMap
    } else {
    }
    if eq(archiveExists, false) then {
      insert archives[disclose(owner)] := emptyMap
    } else {
    }
    reset ordinary[disclose(owner)][disclose(bucket)]
    reset archives[disclose(owner)][disclose(bucket)]
    insertHash ordinary[disclose(owner)][disclose(bucket)] := disclose(leafHash)
    insertField archives[disclose(owner)][disclose(bucket)] := disclose(leaf)
  end

  entry append uses nestedMerkleWrite where
    insertHash ordinary[disclose(owner)][disclose(bucket)] := disclose(leafHash)
    insertField archives[disclose(owner)][disclose(bucket)] := disclose(leaf)
  end

  entry setIndex uses nestedMerkleIndexed where
    insertFieldIndex ordinary[disclose(owner)][disclose(bucket)] at 2 := disclose(leaf)
    insertHashIndex archives[disclose(owner)][disclose(bucket)] at disclose(position) := disclose(leafHash)
  end

  entry readTrees uses nestedMerkleQuery where
    checkRoot ordinary[disclose(owner)][disclose(bucket)] against disclose(digest) as matchesOrdinary
    checkRoot archives[disclose(owner)][disclose(bucket)] against disclose(digest) as matchesArchive
    isFull ordinary[disclose(owner)][disclose(bucket)] as ordinaryAtCapacity
    isFull archives[disclose(owner)][disclose(bucket)] as archiveAtCapacity
    return ordinaryKnown : Bool := matchesOrdinary
    return archiveKnown : Bool := matchesArchive
    return ordinaryFull : Bool := ordinaryAtCapacity
    return archiveFull : Bool := archiveAtCapacity
  end

  entry clear uses nestedMerklePath where
    resetHistory archives[disclose(owner)][disclose(bucket)]
  end

  entry resetTrees uses nestedMerklePath where
    reset ordinary[disclose(owner)][disclose(bucket)]
    reset archives[disclose(owner)][disclose(bucket)]
  end
end

open Noctium

private def nestedMerkleModel : Except String _root_.Bool := do
  let lookupEntry := fun name => NativeNestedMerkle.entrypoints.find? (·.name == name)
  let some setupEntry := lookupEntry "setup" | throw "missing setup"
  let some readEntry := lookupEntry "readTrees" | throw "missing readTrees"
  let ctx : EvalContext := {modulus := Field.modulus, poseidon2 := fun _ _ _ => .error "unused"}
  let path := [("owner", Value.bytes 32 (List.replicate 32 7)), ("bucket", Value.native 1)]
  let empty : LedgerState := {trees := [("ordinary", .map []), ("archives", .map [])]}
  let (_, initialized) ← setupEntry.run ctx path empty
  let (outputs, after) ← readEntry.run ctx (("digest", .native 0) :: path) initialized
  pure (outputs.lookup "ordinaryKnown" == some (.bool Bool.true) &&
    outputs.lookup "archiveKnown" == some (.bool Bool.true) && after == initialized)

#guard match nestedMerkleModel with
  | .ok result => result
  | .error _ => Bool.false

#guard
  match NativeNestedMerkle.entrypoints.find? (·.name == "resetTrees") with
  | none => Bool.false
  | some resetEntry =>
    let privatePath : List PathKey := [.mk (.bytes 32) (.ref "owner"), .mk .native (.native 1)]
    let privateReset := Effect.merkleTreeResetAt "ordinary" privatePath 2 Bool.false
    let subject := {resetEntry with effects := privateReset :: resetEntry.effects.drop 1}
    match Disclosure.entrypoint subject with
    | .error diagnostic => diagnostic.message.contains "undisclosed private parameter 'owner'"
    | .ok _ => Bool.false
