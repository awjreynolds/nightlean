import Noctium.Frontend

open scoped Noctium
open Noctium

noctium_circuit recordMerkleInputs where
  private tag : Bytes 3
  private accepted : Bool
  private count : UInt 16
  private position : UInt 64
  public enabled : Bool
end

noctium_contract NativeRecordMerkleLeaves where
  merkleTree ordinary : 2 of struct Leaf {
    payload : Bytes 3
    approved : Bool
    counterValue : UInt 16
  }
  historicMerkleTree archive : 2 of struct Leaf {
    payload : Bytes 3
    approved : Bool
    counterValue : UInt 16
  }

  entry append uses recordMerkleInputs where
    insertLeaf ordinary := fields(disclose(tag), disclose(accepted), disclose(count))
    insertLeaf archive := fields(disclose(tag), disclose(accepted), disclose(count))
  end

  entry setIndex uses recordMerkleInputs where
    when enabled insertLeafIndex ordinary at disclose(position) :=
      fields(disclose(tag), disclose(accepted), disclose(count))
    when enabled insertLeafIndex archive at disclose(position) :=
      fields(disclose(tag), disclose(accepted), disclose(count))
  end

  entry setDefault uses recordMerkleInputs where
    when enabled insertLeafDefault ordinary at disclose(position)
    when enabled insertLeafDefault archive at disclose(position)
  end
end

private def checkRecordPreimages : Except String _root_.Bool := do
  let [appendCall, _, defaultCall] := NativeRecordMerkleLeaves.entrypoints
    | throw "expected append, index and default entrypoints"
  let context : EvalContext := {
    modulus := Field.modulus
    poseidon2 := fun _ _ _ => .error "unused"
    persistentHash32 := fun bytes =>
      pure ((bytes.length :: bytes) ++ List.replicate (31 - bytes.length) 0)
  }
  let inputs := [("tag", Value.bytes 3 [12, 0, 0]), ("accepted", Value.bool Bool.true),
    ("count", Value.uint 65535 258)]
  let domain := [109, 100, 110, 58, 108, 104]
  let check (call : Entrypoint) (payload : List Nat) : Except String _root_.Bool := do
    let hashes := call.effects.filterMap fun effect => match effect with
      | .merkleTreeInsertHash _ hash | .merkleTreeInsertHashIndex _ hash _ => some hash
      | _ => none
    let actual ← hashes.mapM fun hash => hash.eval context inputs
    let expected := domain ++ payload
    pure (actual == List.replicate 2 ((expected.length :: expected) ++ List.replicate 19 0))
  pure ((← check appendCall [12, 0, 0, 1, 2, 1]) && (← check defaultCall (List.replicate 6 0)))

#guard checkRecordPreimages.toOption == some Bool.true

/-- ledger record field count does not match its checked layout -/
#guard_msgs (substring := true) in
noctium_contract MalformedRecordLeaf where
  merkleTree claims : 2 of struct Leaf { flag : Bool size : UInt 16 }
  entry put uses recordMerkleInputs where
    insertLeaf claims := fields(disclose(accepted))
  end
end

/-- undisclosed private parameter 'accepted' -/
#guard_msgs (substring := true) in
noctium_contract UndisclosedRecordLeaf where
  merkleTree claims : 2 of struct Leaf { flag : Bool size : UInt 16 }
  entry put uses recordMerkleInputs where
    insertLeaf claims := fields(accepted, disclose(count))
  end
end
