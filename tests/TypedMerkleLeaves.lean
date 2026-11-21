import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit typedMerkleInputs where
  private owner : Bytes32
  private leaf : Bool
  private position : UInt 64
  public enabled : Bool
end

noctium_contract NativeTypedMerkleLeaves where
  merkleTree ordinary : 2 of Bool
  tree archives : Bytes32 => HistoricMerkleTree 2 of Bool

  entry setup uses typedMerkleInputs where
    reset archives[disclose(owner)]
  end

  entry append uses typedMerkleInputs where
    insertLeaf ordinary := disclose(leaf)
    insertLeaf archives[disclose(owner)] := disclose(leaf)
  end

  entry setIndex uses typedMerkleInputs where
    when enabled insertLeafIndex ordinary at disclose(position) := disclose(leaf)
    when enabled insertLeafIndex archives[disclose(owner)] at disclose(position) := disclose(leaf)
  end

  entry setDefault uses typedMerkleInputs where
    when enabled insertLeafDefault ordinary at disclose(position)
    when enabled insertLeafDefault archives[disclose(owner)] at disclose(position)
  end
end

noctium_circuit leafEncodingInputs where
  private singleton : UIntRange 1
  private count : UInt 16
  private tag : Bytes 3
end

noctium_contract MerkleLeafEncodings where
  merkleTree singletons : 2 of UIntRange 1
  historicMerkleTree counts : 2 of UInt 16
  tree tags : Native => Native => MerkleTree 2 of Bytes 3

  entry encodeLeaves uses leafEncodingInputs where
    insertLeaf singletons := disclose(singleton)
    insertLeaf counts := disclose(count)
    insertDefault tags[1]
    insertDefault tags[1][2]
    insertLeaf tags[1][2] := disclose(tag)
  end
end

private def checkLeafPreimages : Except String _root_.Bool := do
  let [operation] := MerkleLeafEncodings.entrypoints | throw "expected encoding entrypoint"
  let context : EvalContext := {
    modulus := Field.modulus
    poseidon2 := fun _ _ _ => .error "unused"
    persistentHash32 := fun preimage =>
      pure ((preimage.length :: preimage) ++ List.replicate (31 - preimage.length) 0)
  }
  let inputs := [("singleton", Value.uint 0 0), ("count", Value.uint 65535 258),
    ("tag", Value.bytes 3 [10, 20, 30])]
  let hashes := operation.effects.filterMap fun effect => match effect with
    | .merkleTreeInsertHash _ hash | .merkleTreeInsertHashAt _ _ hash => some hash
    | _ => none
  let actual ← hashes.mapM fun hash => hash.eval context inputs
  let domain := [109, 100, 110, 58, 108, 104]
  let expected := [[0], [2, 1], [10, 20, 30]].map fun leaf =>
    let preimage := domain ++ leaf
    (preimage.length :: preimage) ++ List.replicate (31 - preimage.length) 0
  pure (actual == expected)

#guard checkLeafPreimages.toOption == some Bool.true

/-- Noctium expression type mismatch -/
#guard_msgs (substring := true) in
noctium_contract MismatchedMerkleLeaf where
  merkleTree claims : 2 of Bytes 1
  entry put uses typedMerkleInputs where
    insertLeaf claims := disclose(leaf)
  end
end

/-- undisclosed private parameter 'leaf' -/
#guard_msgs (substring := true) in
noctium_contract UndisclosedTypedMerkleLeaf where
  merkleTree claims : 2 of Bool
  entry put uses typedMerkleInputs where
    insertLeaf claims := leaf
  end
end
