import Noctium.Frontend
import Noctium.Disclosure
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit jubjubMerkleInputs where
  private point : JubjubPoint
  private position : UInt 64
  public enabled : Bool
end

noctium_contract JubjubMerkleLeaves where
  merkleTree points : 2 of JubjubPoint

  entry append uses jubjubMerkleInputs where
    insertLeaf points := disclose(point)
  end

  entry appendAt uses jubjubMerkleInputs where
    when enabled insertLeafIndex points at disclose(position) := disclose(point)
  end

  entry defaultAt uses jubjubMerkleInputs where
    when enabled insertLeafDefault points at disclose(position)
  end
end

private def pointMerkleWriteHash (call : Entrypoint) : Option (Expr (.bytes 32)) :=
  call.effects.findSome? fun effect =>
    match effect with
    | .merkleTreeInsertHash _ hash | .merkleTreeInsertHashAt _ _ hash => some hash
    | .merkleTreeInsertHashIndex _ hash _ | .merkleTreeInsertHashIndexAt _ _ hash _ => some hash
    | _ => none

private def pinnedIdentityPreimage : List Nat :=
  [109, 100, 110, 58, 108, 104] ++ List.replicate 32 0 ++ [1] ++ List.replicate 31 0

private def pinnedIdentityLeafHash : List Nat :=
  [180, 208, 99, 126, 197, 38, 239, 220, 114, 29, 226, 139, 83, 91, 18, 141,
    201, 2, 130, 61, 163, 39, 79, 84, 105, 215, 153, 109, 110, 95, 240, 185]

private def pointMerkleContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused"
  persistentHash32 := fun preimage =>
    if preimage == pinnedIdentityPreimage then pure pinnedIdentityLeafHash
    else .error "unexpected JubjubPoint Merkle leaf encoding"
  jubjub := {
    pointValid := fun point =>
      if point == (0, 1) then pure () else .error "unexpected point"
    fromCoordinates := fun x y => pure (x, y)
  }
}

private def checkPinnedPointLeaf : Except String _root_.Bool := do
  let some append := JubjubMerkleLeaves.entrypoints.find? (·.name == "append")
    | throw "missing append entrypoint"
  let some appendAt := JubjubMerkleLeaves.entrypoints.find? (·.name == "appendAt")
    | throw "missing indexed append entrypoint"
  let some defaultAt := JubjubMerkleLeaves.entrypoints.find? (·.name == "defaultAt")
    | throw "missing default entrypoint"
  let some appendHash := pointMerkleWriteHash append | throw "append has no Merkle write"
  let some indexedHash := pointMerkleWriteHash appendAt | throw "indexed append has no Merkle write"
  let some defaultHash := pointMerkleWriteHash defaultAt | throw "default append has no Merkle write"
  let inputs := [
    ("point", Value.jubjubPoint 0 1),
    ("position", Value.uint (2 ^ 64 - 1) 0),
    ("enabled", Value.bool _root_.Bool.true)]
  let expected := pinnedIdentityLeafHash
  pure ((← appendHash.eval pointMerkleContext inputs) == expected &&
    (← indexedHash.eval pointMerkleContext inputs) == expected &&
    (← defaultHash.eval pointMerkleContext inputs) == expected)

#guard checkPinnedPointLeaf.toOption == some _root_.Bool.true

private def guardedIndexUsesPublicEnable : _root_.Bool :=
  match JubjubMerkleLeaves.entrypoints.find? (·.name == "appendAt") with
  | some call =>
    match call.effectGuards with
    | [some (.ref name)] => name == "enabled"
    | _ => _root_.Bool.false
  | none => _root_.Bool.false

#guard guardedIndexUsesPublicEnable

private def disclosedPointWritePasses : _root_.Bool :=
  match JubjubMerkleLeaves.entrypoints.find? (·.name == "appendAt") with
  | some call => (Disclosure.entrypoint call).isOk
  | none => _root_.Bool.false

#guard disclosedPointWritePasses

private def pointMerkleWritesLowerToNative : _root_.Bool :=
  JubjubMerkleLeaves.entrypoints.all fun call =>
    (Backend.Zkir.lowerEntrypoint JubjubMerkleLeaves.state call).isOk

#guard pointMerkleWritesLowerToNative

/-- undisclosed private parameter 'point' -/
#guard_msgs (substring := true) in
noctium_contract UndisclosedJubjubMerkleLeaf where
  merkleTree points : 2 of JubjubPoint
  entry append uses jubjubMerkleInputs where
    insertLeaf points := point
  end
end
