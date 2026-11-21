import Noctium.Frontend
import Noctium.Backend.Zkir

open scoped Noctium
open Noctium

noctium_circuit foreignMerkleInputs where
  private k1Base : Secp256k1Base
  private k1Scalar : Secp256k1Scalar
  private k1Point : Secp256k1Point
  private r1Base : Secp256r1Base
  private r1Scalar : Secp256r1Scalar
  private r1Point : Secp256r1Point
  private c255Base : Curve25519Base
  private c255Scalar : Curve25519Scalar
  private c255Point : Curve25519Point
end

noctium_contract ForeignMerkleLeaves where
  merkleTree k1BaseTree : 2 of Secp256k1Base
  merkleTree k1ScalarTree : 2 of Secp256k1Scalar
  merkleTree k1PointTree : 2 of Secp256k1Point
  merkleTree r1BaseTree : 2 of Secp256r1Base
  merkleTree r1ScalarTree : 2 of Secp256r1Scalar
  merkleTree r1PointTree : 2 of Secp256r1Point
  historicMerkleTree c255BaseTree : 2 of Curve25519Base
  historicMerkleTree c255ScalarTree : 2 of Curve25519Scalar
  historicMerkleTree c255PointTree : 2 of Curve25519Point

  entry append uses foreignMerkleInputs where
    insertLeaf k1BaseTree := disclose(k1Base)
    insertLeaf k1ScalarTree := disclose(k1Scalar)
    insertLeaf k1PointTree := disclose(k1Point)
    insertLeaf r1BaseTree := disclose(r1Base)
    insertLeaf r1ScalarTree := disclose(r1Scalar)
    insertLeaf r1PointTree := disclose(r1Point)
    insertLeaf c255BaseTree := disclose(c255Base)
    insertLeaf c255ScalarTree := disclose(c255Scalar)
    insertLeaf c255PointTree := disclose(c255Point)
  end
end

private def foreignMerkleWrites : List String :=
  match ForeignMerkleLeaves.entrypoints with
  | [call] => call.effects.filterMap fun effect =>
      match effect with
      | .merkleTreeInsertHash storage _ => some storage
      | _ => none
  | _ => []

#guard foreignMerkleWrites == [
  "k1BaseTree", "k1ScalarTree", "k1PointTree", "r1BaseTree", "r1ScalarTree",
  "r1PointTree", "c255BaseTree", "c255ScalarTree", "c255PointTree"]

#guard ForeignMerkleLeaves.entrypoints.all fun call =>
  (Backend.Zkir.lowerEntrypoint ForeignMerkleLeaves.state call).isOk
