import Noctium.Frontend
import Noctium.Backend.Impact
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit emptyCircuit where
end

noctium_circuit insertHashCircuit where
  private leafHash : Bytes32
end

noctium_circuit checkRootCircuit where
  public active : Bool
  private expectedRoot : Native
end

noctium_circuit appendAndCheckCircuit where
  private leafHash : Bytes32
  private expectedRoot : Native
end

noctium_contract NativeMerkleTree where
  merkleTree claims : 2
  entry fullStatus uses emptyCircuit where
    isFull claims as full
    return fullStatus : Bool := full
  end
  entry resetAndCheck uses emptyCircuit where
    reset claims
    isFull claims as resetFull
    return resetStatus : Bool := resetFull
  end
  entry append uses insertHashCircuit where
    insertHash claims := disclose(leafHash)
    isFull claims as appendFull
    return fullStatus : Bool := appendFull
  end
  entry checkCurrent uses checkRootCircuit where
    when active checkRoot claims against disclose(expectedRoot) as rootMatches
    return isValid : Bool := rootMatches
  end
  entry appendAndCheck uses appendAndCheckCircuit where
    insertHash claims := disclose(leafHash)
    checkRoot claims against disclose(expectedRoot) as rootMatches
    return isValid : Bool := rootMatches
  end
end

private def merkleTreeContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
  transientHash := fun values => .ok (values.foldl (· + ·) 0 % Field.modulus)
}

private def sevenLeafRoot : Nat :=
  match Noctium.Merkle.Tree.insertHash merkleTreeContext.transientHash
      merkleTreeContext.modulus 2 0 (List.replicate 32 7) Noctium.Merkle.Tree.empty with
  | .ok tracked => tracked.root
  | .error _ => 0

#guard match NativeMerkleTree.entrypoints.find? (·.name == "resetAndCheck") with
  | some ep =>
    match ep.run merkleTreeContext [] {
      trees := [("claims", .merkleTree 2 4)]
    } with
    | .ok (outputs, after) =>
      outputs.lookup "resetStatus" == some (.bool Bool.false) &&
      after.trees.lookup "claims" == some (.merkleTree 2 0)
    | .error _ => Bool.false
  | none => Bool.false

#guard match NativeMerkleTree.entrypoints.find? (·.name == "append") with
  | some ep =>
    let hash := Value.bytes 32 (List.replicate 32 7)
    match ep.run merkleTreeContext [("leafHash", hash)] {
      trees := [("claims", .merkleTree 2 0)]
    } with
    | .ok (outputs, after) =>
      outputs.lookup "fullStatus" == some (.bool Bool.false) &&
      (match after.trees.lookup "claims" with
       | some (.merkleTreeKnown 2 1 tracked) => tracked.root == sevenLeafRoot
       | _ => Bool.false)
    | .error _ => Bool.false
  | none => Bool.false

#guard match NativeMerkleTree.entrypoints.find? (·.name == "append") with
  | some ep =>
    match ep.run merkleTreeContext [("leafHash", Value.bytes 32 (List.replicate 32 7))] {
      trees := [("claims", .merkleTree 2 4)]
    } with
    | .error message => message == "MerkleTree is full"
    | .ok _ => Bool.false
  | none => Bool.false

/-- undisclosed private parameter -/
#guard_msgs (substring := true) in
noctium_contract UndisclosedMerkleAppend where
  merkleTree claims : 2
  entry append uses insertHashCircuit where
    insertHash claims := leafHash
  end
end

private def checkRootModel : Except String _root_.Bool := do
  let some checkCurrent := NativeMerkleTree.entrypoints.find? (·.name == "checkCurrent")
    | throw "missing checkCurrent"
  let some appendAndCheck := NativeMerkleTree.entrypoints.find? (·.name == "appendAndCheck")
    | throw "missing appendAndCheck"
  let initial : LedgerState := {trees := [("claims", .merkleTree 2 0)]}
  let check := fun active expected => checkCurrent.run merkleTreeContext
    [("active", .bool active), ("expectedRoot", .native expected)] initial
  let (empty, _) ← check Bool.true 0
  let (mismatch, _) ← check Bool.true 1
  let (skipped, _) ← check Bool.false 0
  let (inserted, _) ← appendAndCheck.run merkleTreeContext
    [("leafHash", .bytes 32 (List.replicate 32 7)), ("expectedRoot", .native sevenLeafRoot)] initial
  pure (empty.lookup "isValid" == some (.bool Bool.true) &&
    mismatch.lookup "isValid" == some (.bool Bool.false) &&
    skipped.lookup "isValid" == some (.bool Bool.false) &&
    inserted.lookup "isValid" == some (.bool Bool.true))

#guard match checkRootModel with
  | .ok result => result
  | .error _ => Bool.false

/-- undisclosed private parameter -/
#guard_msgs (substring := true) in
noctium_contract UndisclosedMerkleRoot where
  merkleTree claims : 2
  entry checkCurrent uses checkRootCircuit where
    when active checkRoot claims against expectedRoot as rootMatches
    return isValid : Bool := rootMatches
  end
end
