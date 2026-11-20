import Lean

namespace Noctium.Merkle

inductive Tree where
  | empty
  | leaf (digest : Nat)
  | branch (digest : Nat) (left right : Tree)
  deriving Repr, BEq

def Tree.root : Tree → Nat
  | .empty => 0
  | .leaf digest | .branch digest .. => digest

private def insertDigest (hash : List Nat → Except String Nat) (modulus : Nat) :
    Nat → Nat → Nat → Tree → Except String Tree
  | 0, 0, digest, .empty => pure (.leaf digest)
  | 0, 0, _, .leaf _ => throw "MerkleTree append does not select an empty leaf"
  | 0, _, _, _ => throw "MerkleTree append does not select an empty leaf"
  | height + 1, index, digest, tree => do
    let (left, right) ← match tree with
      | .empty => pure (.empty, .empty)
      | .branch _ left right => pure (left, right)
      | .leaf _ => throw "MerkleTree shape differs from its depth"
    let half := 2 ^ height
    let (left, right) ← if index < half then
        pure (← insertDigest hash modulus height index digest left, right)
      else pure (left, ← insertDigest hash modulus height (index - half) digest right)
    let root ← hash [left.root, right.root]
    unless root < modulus do throw "MerkleTree hash is outside the native field"
    pure (.branch root left right)

/-- Append Bytes32 at the cursor, using its low 31 little-endian bytes as a field leaf. -/
def Tree.insertHash (hash : List Nat → Except String Nat) (modulus depth index : Nat)
    (bytes : List Nat) (tree : Tree) : Except String Tree := do
  unless 2 ≤ depth && depth ≤ 32 do throw "MerkleTree depth must be between 2 and 32"
  unless index < 2 ^ depth do throw "MerkleTree is full"
  unless bytes.length == 32 && bytes.all (· < 256) do throw "MerkleTree hash must be Bytes32"
  let digest := (bytes.take 31).foldr (fun byte rest => byte + 256 * rest) 0
  unless digest < modulus do throw "MerkleTree leaf is outside the native field"
  insertDigest hash modulus depth index digest tree

end Noctium.Merkle
