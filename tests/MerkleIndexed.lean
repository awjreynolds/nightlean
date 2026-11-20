import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit indexedHashInputs where
  private position : UInt 64
  private leafHash : Bytes32
end

noctium_circuit indexedFieldInputs where
  private position : UInt 64
  private leaf : Native
end

noctium_circuit guardedIndexedInputs where
  public active : Bool
  private position : UInt 64
  private leafHash : Bytes32
end

noctium_contract NativeMerkleIndexed where
  merkleTree claims : 2
  entry writeHashIndex uses indexedHashInputs where
    insertHashIndex claims at disclose(position) := disclose(leafHash)
    isFull claims as full
    return fullStatus : Bool := full
  end
  entry writeFieldIndex uses indexedFieldInputs where
    insertFieldIndex claims at disclose(position) := disclose(leaf)
    isFull claims as full
    return fullStatus : Bool := full
  end
  entry guardedHashIndex uses guardedIndexedInputs where
    when active insertHashIndex claims at disclose(position) := disclose(leafHash)
    isFull claims as full
    return fullStatus : Bool := full
  end
end

private def model : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
  transientHash := fun values => match values with
    | [left, right] => pure (left + 2 * right)
    | _ => .error "expected a pair of Merkle roots"
}

private def modelIndexed : Except String _root_.Bool := do
  let some ep := NativeMerkleIndexed.entrypoints.find? (·.name == "writeHashIndex")
    | throw "missing indexed hash entrypoint"
  let inputs := fun position digest => [
    ("position", Value.uint (2 ^ 64 - 1) position),
    ("leafHash", Value.bytes 32 (digest :: List.replicate 31 0))]
  let (_, sparse) ← ep.run model (inputs 2 1) {trees := [("claims", .merkleTree 2 0)]}
  let (_, lower) ← ep.run model (inputs 0 3) sparse
  let (_, replaced) ← ep.run model (inputs 2 4) lower
  match replaced.trees.lookup "claims" with
  | some (.merkleTreeKnown 2 3 tracked) => pure (tracked.root == 11)
  | _ => pure Bool.false

#guard match modelIndexed with
  | .ok result => result
  | .error _ => Bool.false

/-- undisclosed private parameter -/
#guard_msgs (substring := true) in
noctium_contract UndisclosedMerkleIndex where
  merkleTree claims : 2
  entry badIndex uses indexedHashInputs where
    insertHashIndex claims at position := disclose(leafHash)
  end
end

/-- undisclosed private parameter -/
#guard_msgs (substring := true) in
noctium_contract UndisclosedIndexedMerkleLeaf where
  merkleTree claims : 2
  entry badLeaf uses indexedFieldInputs where
    insertFieldIndex claims at disclose(position) := leaf
  end
end
