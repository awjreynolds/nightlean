import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit foreignStorageValues where
  private kBase : Secp256k1Base
  private kScalar : Secp256k1Scalar
  private kPoint : Secp256k1Point
  private rBase : Secp256r1Base
  private rScalar : Secp256r1Scalar
  private rPoint : Secp256r1Point
end

noctium_contract ForeignStorage where
  cell kBaseCell : Secp256k1Base
  cell kScalarCell : Secp256k1Scalar
  cell kPointCell : Secp256k1Point
  cell rBaseCell : Secp256r1Base
  cell rScalarCell : Secp256r1Scalar
  cell rPointCell : Secp256r1Point
  map kBaseMap : Native => Secp256k1Base
  map kScalarMap : Native => Secp256k1Scalar
  map kPointMap : Native => Secp256k1Point
  map rBaseMap : Bytes32 => Secp256r1Base
  map rScalarMap : Bytes32 => Secp256r1Scalar
  map rPointMap : Bytes32 => Secp256r1Point
  constructor() where
    initialize kBaseCell := secp256k1Base(0)
    initialize kScalarCell := secp256k1Scalar(0)
    initialize kPointCell := secp256k1Identity()
    initialize rBaseCell := secp256r1Base(0)
    initialize rScalarCell := secp256r1Scalar(0)
    initialize rPointCell := secp256r1Identity()
  end
  entry update uses foreignStorageValues where
    read kBaseCell as initialKBase
    read kScalarCell as initialKScalar
    read kPointCell as initialKPoint
    read rBaseCell as initialRBase
    read rScalarCell as initialRScalar
    read rPointCell as initialRPoint
    member kBaseMap[9999] as kBaseMapExists
    member kScalarMap[9999] as kScalarMapExists
    member kPointMap[9999] as kPointMapExists
    member rBaseMap[bytes32("missing-base")] as rBaseMapExists
    member rScalarMap[bytes32("missing-scalar")] as rScalarMapExists
    member rPointMap[bytes32("missing-point")] as rPointMapExists
    when eq(kBaseMapExists, true) read kBaseMap[9999] as missingKBaseMapValue
    when eq(kScalarMapExists, true) read kScalarMap[9999] as missingKScalarMapValue
    when eq(kPointMapExists, true) read kPointMap[9999] as missingKPointMapValue
    when eq(rBaseMapExists, true) read rBaseMap[bytes32("missing-base")] as missingRBaseMapValue
    when eq(rScalarMapExists, true) read rScalarMap[bytes32("missing-scalar")] as missingRScalarMapValue
    when eq(rPointMapExists, true) read rPointMap[bytes32("missing-point")] as missingRPointMapValue
    write kBaseCell := disclose(kBase)
    write kScalarCell := disclose(kScalar)
    write kPointCell := disclose(kPoint)
    write rBaseCell := disclose(rBase)
    write rScalarCell := disclose(rScalar)
    write rPointCell := disclose(rPoint)
    read kBaseCell as kBaseCellRead
    read kScalarCell as kScalarCellRead
    read kPointCell as kPointCellRead
    read rBaseCell as rBaseCellRead
    read rScalarCell as rScalarCellRead
    read rPointCell as rPointCellRead
    insert kBaseMap[11] := disclose(kBase)
    insert kScalarMap[12] := disclose(kScalar)
    insert kPointMap[13] := disclose(kPoint)
    insert rBaseMap[bytes32("r-base")] := disclose(rBase)
    insert rScalarMap[bytes32("r-scalar")] := disclose(rScalar)
    insert rPointMap[bytes32("r-point")] := disclose(rPoint)
    read kBaseMap[11] as kBaseMapRead
    read kScalarMap[12] as kScalarMapRead
    read kPointMap[13] as kPointMapRead
    read rBaseMap[bytes32("r-base")] as rBaseMapRead
    read rScalarMap[bytes32("r-scalar")] as rScalarMapRead
    read rPointMap[bytes32("r-point")] as rPointMapRead
    return oldKBase : Secp256k1Base := disclose(initialKBase)
    return oldKScalar : Secp256k1Scalar := disclose(initialKScalar)
    return oldKPoint : Secp256k1Point := disclose(initialKPoint)
    return oldRBase : Secp256r1Base := disclose(initialRBase)
    return oldRScalar : Secp256r1Scalar := disclose(initialRScalar)
    return oldRPoint : Secp256r1Point := disclose(initialRPoint)
    return missingKBaseMap : Secp256k1Base := disclose(missingKBaseMapValue)
    return missingKScalarMap : Secp256k1Scalar := disclose(missingKScalarMapValue)
    return missingKPointMap : Secp256k1Point := disclose(missingKPointMapValue)
    return missingRBaseMap : Secp256r1Base := disclose(missingRBaseMapValue)
    return missingRScalarMap : Secp256r1Scalar := disclose(missingRScalarMapValue)
    return missingRPointMap : Secp256r1Point := disclose(missingRPointMapValue)
    return kBaseCellResult : Secp256k1Base := disclose(kBaseCellRead)
    return kScalarCellResult : Secp256k1Scalar := disclose(kScalarCellRead)
    return kPointCellResult : Secp256k1Point := disclose(kPointCellRead)
    return rBaseCellResult : Secp256r1Base := disclose(rBaseCellRead)
    return rScalarCellResult : Secp256r1Scalar := disclose(rScalarCellRead)
    return rPointCellResult : Secp256r1Point := disclose(rPointCellRead)
    return kBaseMapResult : Secp256k1Base := disclose(kBaseMapRead)
    return kScalarMapResult : Secp256k1Scalar := disclose(kScalarMapRead)
    return kPointMapResult : Secp256k1Point := disclose(kPointMapRead)
    return rBaseMapResult : Secp256r1Base := disclose(rBaseMapRead)
    return rScalarMapResult : Secp256r1Scalar := disclose(rScalarMapRead)
    return rPointMapResult : Secp256r1Point := disclose(rPointMapRead)
  end
end

private def foreignStorageEntry : Entrypoint :=
  match ForeignStorage.entrypoints with
  | ep :: _ => ep
  | [] => {name := "missing", circuit := {name := "missing"}}

#guard match ForeignStorage.validate Capabilities.source with
  | .ok _ => _root_.Bool.true
  | .error _ => _root_.Bool.false

#guard foreignStorageEntry.returns.map Output.nativeReturnFieldCount ==
  [2, 2, 5, 2, 2, 5, 2, 2, 5, 2, 2, 5,
    2, 2, 5, 2, 2, 5, 2, 2, 5, 2, 2, 5]

private def foreignStorageK1Generator : Foreign.Point :=
  .affine
    0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
    0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

private def foreignStorageR1Generator : Foreign.Point :=
  .affine
    0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
    0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5

private def foreignStorageBoundaryInputs : EvalEnv := [
  ("kBase", .foreignBase .secp256k1 (Foreign.Curve.baseModulus .secp256k1 - 1)),
  ("kScalar", .foreignScalar .secp256k1 (Foreign.Curve.scalarModulus .secp256k1 - 1)),
  ("kPoint", .foreignPoint .secp256k1 foreignStorageK1Generator),
  ("rBase", .foreignBase .secp256r1 (Foreign.Curve.baseModulus .secp256r1 - 1)),
  ("rScalar", .foreignScalar .secp256r1 (Foreign.Curve.scalarModulus .secp256r1 - 1)),
  ("rPoint", .foreignPoint .secp256r1 foreignStorageR1Generator)]

private def foreignStorageInitial : LedgerState := {
  cells := [
    ("kBaseCell", .foreignBase .secp256k1 0),
    ("kScalarCell", .foreignScalar .secp256k1 0),
    ("kPointCell", .foreignPoint .secp256k1 .identity),
    ("rBaseCell", .foreignBase .secp256r1 0),
    ("rScalarCell", .foreignScalar .secp256r1 0),
    ("rPointCell", .foreignPoint .secp256r1 .identity)]
  maps := [
    ("kBaseMap", [(.native 11, .foreignBase .secp256k1 0),
      (.native 111, .foreignBase .secp256k1 1)]),
    ("kScalarMap", [(.native 12, .foreignScalar .secp256k1 0),
      (.native 112, .foreignScalar .secp256k1 1)]),
    ("kPointMap", [(.native 13, .foreignPoint .secp256k1 .identity),
      (.native 113, .foreignPoint .secp256k1 .identity)]),
    ("rBaseMap", [(.bytes 32 ([114, 45, 98, 97, 115, 101] ++ List.replicate 26 0),
      .foreignBase .secp256r1 0),
      (.bytes 32 ([115, 105, 98, 108, 105, 110, 103] ++ List.replicate 25 0),
        .foreignBase .secp256r1 1)]),
    ("rScalarMap", [(.bytes 32 ([114, 45, 115, 99, 97, 108, 97, 114] ++ List.replicate 24 0),
      .foreignScalar .secp256r1 0),
      (.bytes 32 ([115, 105, 98, 108, 105, 110, 103] ++ List.replicate 25 0),
        .foreignScalar .secp256r1 1)]),
    ("rPointMap", [(.bytes 32 ([114, 45, 112, 111, 105, 110, 116] ++ List.replicate 25 0),
      .foreignPoint .secp256r1 .identity),
      (.bytes 32 ([115, 105, 98, 108, 105, 110, 103] ++ List.replicate 25 0),
        .foreignPoint .secp256r1 .identity)])]
}

private def foreignStorageContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

private def foreignStorageRun : Except String (EvalEnv × LedgerState) :=
  foreignStorageEntry.run foreignStorageContext foreignStorageBoundaryInputs
    foreignStorageInitial

#guard match foreignStorageRun with
  | .ok (outputs, after) =>
    let kBase := Foreign.Curve.baseModulus .secp256k1 - 1
    let kScalar := Foreign.Curve.scalarModulus .secp256k1 - 1
    let rBase := Foreign.Curve.baseModulus .secp256r1 - 1
    let rScalar := Foreign.Curve.scalarModulus .secp256r1 - 1
    outputs.lookup "oldKBase" == some (.foreignBase .secp256k1 0) &&
    outputs.lookup "oldKScalar" == some (.foreignScalar .secp256k1 0) &&
    outputs.lookup "oldKPoint" == some (.foreignPoint .secp256k1 .identity) &&
    outputs.lookup "oldRBase" == some (.foreignBase .secp256r1 0) &&
    outputs.lookup "oldRScalar" == some (.foreignScalar .secp256r1 0) &&
    outputs.lookup "oldRPoint" == some (.foreignPoint .secp256r1 .identity) &&
    outputs.lookup "missingKBaseMap" == some (.foreignBase .secp256k1 0) &&
    outputs.lookup "missingKScalarMap" == some (.foreignScalar .secp256k1 0) &&
    outputs.lookup "missingKPointMap" == some (.foreignPoint .secp256k1 .identity) &&
    outputs.lookup "missingRBaseMap" == some (.foreignBase .secp256r1 0) &&
    outputs.lookup "missingRScalarMap" == some (.foreignScalar .secp256r1 0) &&
    outputs.lookup "missingRPointMap" == some (.foreignPoint .secp256r1 .identity) &&
    outputs.lookup "kBaseCellResult" == some (.foreignBase .secp256k1 kBase) &&
    outputs.lookup "kScalarCellResult" == some (.foreignScalar .secp256k1 kScalar) &&
    outputs.lookup "kPointCellResult" == some (.foreignPoint .secp256k1 foreignStorageK1Generator) &&
    outputs.lookup "rBaseCellResult" == some (.foreignBase .secp256r1 rBase) &&
    outputs.lookup "rScalarCellResult" == some (.foreignScalar .secp256r1 rScalar) &&
    outputs.lookup "rPointCellResult" == some (.foreignPoint .secp256r1 foreignStorageR1Generator) &&
    outputs.lookup "kBaseMapResult" == some (.foreignBase .secp256k1 kBase) &&
    outputs.lookup "kScalarMapResult" == some (.foreignScalar .secp256k1 kScalar) &&
    outputs.lookup "kPointMapResult" == some (.foreignPoint .secp256k1 foreignStorageK1Generator) &&
    outputs.lookup "rBaseMapResult" == some (.foreignBase .secp256r1 rBase) &&
    outputs.lookup "rScalarMapResult" == some (.foreignScalar .secp256r1 rScalar) &&
    outputs.lookup "rPointMapResult" == some (.foreignPoint .secp256r1 foreignStorageR1Generator) &&
    after.cells.lookup "kBaseCell" == some (.foreignBase .secp256k1 kBase) &&
    after.cells.lookup "kScalarCell" == some (.foreignScalar .secp256k1 kScalar) &&
    after.cells.lookup "kPointCell" == some (.foreignPoint .secp256k1 foreignStorageK1Generator) &&
    after.cells.lookup "rBaseCell" == some (.foreignBase .secp256r1 rBase) &&
    after.cells.lookup "rScalarCell" == some (.foreignScalar .secp256r1 rScalar) &&
    after.cells.lookup "rPointCell" == some (.foreignPoint .secp256r1 foreignStorageR1Generator) &&
    after.maps.lookup "kBaseMap" == some [
      (.native 11, .foreignBase .secp256k1 kBase),
      (.native 111, .foreignBase .secp256k1 1)] &&
    after.maps.lookup "kScalarMap" == some [
      (.native 12, .foreignScalar .secp256k1 kScalar),
      (.native 112, .foreignScalar .secp256k1 1)] &&
    after.maps.lookup "kPointMap" == some [
      (.native 13, .foreignPoint .secp256k1 foreignStorageK1Generator),
      (.native 113, .foreignPoint .secp256k1 .identity)] &&
    after.maps.lookup "rBaseMap" == some [
      (.bytes 32 ([114, 45, 98, 97, 115, 101] ++ List.replicate 26 0),
        .foreignBase .secp256r1 rBase),
      (.bytes 32 ([115, 105, 98, 108, 105, 110, 103] ++ List.replicate 25 0),
        .foreignBase .secp256r1 1)] &&
    after.maps.lookup "rScalarMap" == some [
      (.bytes 32 ([114, 45, 115, 99, 97, 108, 97, 114] ++ List.replicate 24 0),
        .foreignScalar .secp256r1 rScalar),
      (.bytes 32 ([115, 105, 98, 108, 105, 110, 103] ++ List.replicate 25 0),
        .foreignScalar .secp256r1 1)] &&
    after.maps.lookup "rPointMap" == some [
      (.bytes 32 ([114, 45, 112, 111, 105, 110, 116] ++ List.replicate 25 0),
        .foreignPoint .secp256r1 foreignStorageR1Generator),
      (.bytes 32 ([115, 105, 98, 108, 105, 110, 103] ++ List.replicate 25 0),
        .foreignPoint .secp256r1 .identity)]
  | .error _ => _root_.Bool.false

#guard match foreignStorageEntry.run foreignStorageContext
    (("kBase", .foreignBase .secp256k1 (Foreign.Curve.baseModulus .secp256k1)) ::
      foreignStorageBoundaryInputs.filter (fun (name, _) => name != "kBase"))
    foreignStorageInitial with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

private def foreignStorageUndisclosedWrite : Entrypoint := {
  name := "foreignStorageUndisclosedWrite"
  circuit := foreignStorageValues
  effects := [.writeCell "kBaseCell" (.foreign (.base .secp256k1))
    (.ref "kBase")]
}

#guard match Disclosure.entrypoint foreignStorageUndisclosedWrite with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
