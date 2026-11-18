import Noctium.Frontend
import Noctium.Disclosure
import Noctium.Backend.NativeProducer

open scoped Noctium
open Noctium
open Lean Noctium.Backend.Native

noctium_circuit foreignOperations where
  private kBase : Secp256k1Base
  private kScalar : Secp256k1Scalar
  private kPoint : Secp256k1Point
  private rBase : Secp256r1Base
  private rScalar : Secp256r1Scalar
  private rPoint : Secp256r1Point
  private raw : Bytes 64
  private enabled : Bool
  private guardInv : Bool
  private guardIdentityX : Bool
  private guardCoordinates : Bool
  private guardDecode : Bool
  let kBaseResult : Secp256k1Base := foreignMul(foreignAdd(kBase, secp256k1Base(2)), foreignInv(kBase))
  let kScalarResult : Secp256k1Scalar := foreignSub(foreignAdd(kScalar, secp256k1Scalar(1)), foreignNeg(kScalar))
  let kPointResult : Secp256k1Point := foreignAdd(curveMul(kPoint, kScalar), curveMulGenerator(kScalar))
  let rBaseResult : Secp256r1Base := foreignMul(foreignAdd(rBase, secp256r1Base(2)), foreignInv(rBase))
  let rScalarResult : Secp256r1Scalar := foreignSub(foreignAdd(rScalar, secp256r1Scalar(1)), foreignNeg(rScalar))
  let rPointResult : Secp256r1Point := foreignAdd(curveMul(rPoint, rScalar), curveMulGenerator(rScalar))
  assert eq(foreignAdd(kBase, foreignNeg(kBase)), secp256k1Base(0))
  assert eq(foreignSub(foreignAdd(kBase, secp256k1Base(1)), secp256k1Base(1)), kBase)
  assert eq(foreignMul(kScalar, foreignInv(kScalar)), secp256k1Scalar(1))
  assert eq(foreignSub(foreignAdd(kScalar, secp256k1Scalar(1)), foreignNeg(kScalar)), kScalarResult)
  assert eq(foreignAdd(kPoint, foreignNeg(kPoint)), secp256k1Identity())
  assert eq(foreignSub(foreignAdd(kPoint, curveMulGenerator(kScalar)), curveMulGenerator(kScalar)), kPoint)
  assert eq(curveFromCoordinates(curveX(kPoint), curveY(kPoint)), kPoint)
  assert eq(foreignFromBytes(Secp256k1Point, foreignToBytes(kPoint)), kPoint)
  assert eq(foreignFromBytes(Secp256k1Base, foreignToBytes(kBase)), kBase)
  assert eq(foreignAdd(rBase, foreignNeg(rBase)), secp256r1Base(0))
  assert eq(foreignSub(foreignAdd(rBase, secp256r1Base(1)), secp256r1Base(1)), rBase)
  assert eq(foreignMul(rScalar, foreignInv(rScalar)), secp256r1Scalar(1))
  assert eq(foreignSub(foreignAdd(rScalar, secp256r1Scalar(1)), foreignNeg(rScalar)), rScalarResult)
  assert eq(foreignAdd(rPoint, foreignNeg(rPoint)), secp256r1Identity())
  assert eq(foreignSub(foreignAdd(rPoint, curveMulGenerator(rScalar)), curveMulGenerator(rScalar)), rPoint)
  assert eq(curveFromCoordinates(curveX(rPoint), curveY(rPoint)), rPoint)
  assert eq(foreignFromBytes(Secp256r1Point, foreignToBytes(rPoint)), rPoint)
  assert eq(foreignFromBytes(Secp256r1Base, foreignToBytes(rBase)), rBase)
  output kBaseValue : Secp256k1Base := disclose(kBaseResult)
  output kScalarValue : Secp256k1Scalar := disclose(kScalarResult)
  output kPointValue : Secp256k1Point := disclose(kPointResult)
  output kPointBytesValue : Bytes 33 := disclose(foreignToBytes(kPointResult))
  output rBaseValue : Secp256r1Base := disclose(rBaseResult)
  output rScalarValue : Secp256r1Scalar := disclose(rScalarResult)
  output rPointValue : Secp256r1Point := disclose(rPointResult)
  output rPointBytesValue : Bytes 33 := disclose(foreignToBytes(rPointResult))
  output rawKBaseValue : Secp256k1Base := disclose(foreignFromBytes(Secp256k1Base, raw))
  output rawRScalarValue : Secp256r1Scalar := disclose(foreignFromBytes(Secp256r1Scalar, raw))
  output emptyKBaseValue : Secp256k1Base := disclose(foreignFromBytes(Secp256k1Base, assertThen(enabled, bytes(0, ""))))
end

noctium_contract ForeignOperations where
  cell inverseMarker : UInt 8
  cell identityXMarker : UInt 8
  cell coordinatesMarker : UInt 8
  cell decodeMarker : UInt 8
  entry inspect uses foreignOperations where
    when disclose(guardInv) write inverseMarker := disclose(byteAt(foreignToBytes(foreignInv(secp256k1Base(0))), 0))
    when disclose(guardIdentityX) write identityXMarker := disclose(byteAt(foreignToBytes(curveX(secp256k1Identity())), 0))
    when disclose(guardCoordinates) write coordinatesMarker := disclose(byteAt(foreignToBytes(curveFromCoordinates(secp256k1Base(0), secp256k1Base(0))), 0))
    when disclose(guardDecode) write decodeMarker := disclose(byteAt(foreignToBytes(foreignFromBytes(Secp256k1Point, bytes(33, "invalid"))), 0))
    return kBaseResult : Secp256k1Base := kBaseValue
    return kScalarResult : Secp256k1Scalar := kScalarValue
    return kPointResult : Secp256k1Point := kPointValue
    return kPointBytes : Bytes 33 := kPointBytesValue
    return rBaseResult : Secp256r1Base := rBaseValue
    return rScalarResult : Secp256r1Scalar := rScalarValue
    return rPointResult : Secp256r1Point := rPointValue
    return rPointBytes : Bytes 33 := rPointBytesValue
    return rawKBase : Secp256k1Base := rawKBaseValue
    return rawRScalar : Secp256r1Scalar := rawRScalarValue
    return emptyKBase : Secp256k1Base := emptyKBaseValue
  end
end

private def foreignOperationsContext : EvalContext := {
  modulus := Field.modulus
  poseidon2 := fun _ _ _ => .error "unused by this fixture"
}

#guard match (Expr.foreignBinary (.add (.base .secp256k1))
    (.foreignBase .secp256k1 9) (.foreignBase .secp256k1 5)).eval
    foreignOperationsContext [] with
  | .ok value => value == 14
  | .error _ => _root_.Bool.false
#guard match (Expr.foreignUnary (.inv (.scalar .secp256r1))
    (.foreignScalar .secp256r1 1)).eval foreignOperationsContext [] with
  | .ok value => value == 1
  | .error _ => _root_.Bool.false
#guard match (Expr.foreignFromBytes (.base .secp256k1) (length := 2)
    (.bytesLiteral 2 [5, 1])).eval foreignOperationsContext [] with
  | .ok value => value == 261
  | .error _ => _root_.Bool.false
#guard match (Expr.foreignToBytes (.foreignBase .secp256k1 261)).eval
    foreignOperationsContext [] with
  | .ok value => value.take 2 == [5, 1] && value.length == 32
  | .error _ => _root_.Bool.false

#guard match (Expr.foreignUnary (.inv (.base .secp256k1))
    (.foreignBase .secp256k1 0)).eval foreignOperationsContext [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
#guard match (Expr.foreignUnary (.x .secp256k1)
    (.foreignIdentity .secp256k1)).eval foreignOperationsContext [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
#guard match (Expr.foreignBinary (.fromCoordinates .secp256k1)
    (.foreignBase .secp256k1 0) (.foreignBase .secp256k1 0)).eval
    foreignOperationsContext [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
#guard match (Expr.foreignFromBytes (.point .secp256k1) (length := 33)
    (.bytesLiteral 33 (List.replicate 33 105))).eval foreignOperationsContext [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
#guard match (Expr.foreignFromBytes (.base .secp256k1) (length := 1025)
    (.bytesLiteral 1025 (List.replicate 1025 0))).validate Capabilities.source [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false
#guard match (Expr.foreignUnary (.inv (.base .secp256k1))
    (.foreignBase .secp256k1 1)).validate
    {Capabilities.source with foreignArithmetic := _root_.Bool.false} [] with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

private def foreignPrivateLeak : Circuit := {
  name := "foreignPrivateLeak"
  inputs := [{name := "secret", ty := .foreign (.base .secp256k1), visibility := .private}]
  outputs := [{name := "leak", ty := .foreign (.base .secp256k1), value :=
    Expr.foreignUnary (.neg (.base .secp256k1)) (Expr.ref "secret")}]
}

#guard match Disclosure.circuit foreignPrivateLeak with
  | .error _ => _root_.Bool.true
  | .ok _ => _root_.Bool.false

private def foreignFromBytesProducerAccepts (inputType : NativeValueType)
    (malformed : _root_.Bool) : _root_.Bool := Id.run do
  let expected : Expected := {
    mode := .relation, inputs := [], groups := [], returns := [], assertions := [], bounds := []}
  let state : State := {
    definitions := [("%bytes", ({term := .input "%bytes", maximum := 0, valueType := inputType} : Fact))]}
  let fields := [
    ("op", toJson ("from_bytes" : String)),
    ("bytes", toJson ("%bytes" : String)),
    ("type", toJson (Foreign.Kind.nativeName (.base .secp256k1))),
    ("output", toJson ("%out" : String))]
  let instruction := Json.mkObj (fields ++ if malformed then
    [("extra", toJson _root_.Bool.true)] else [])
  return (validateInstruction expected state instruction).isOk

#guard foreignFromBytesProducerAccepts (.bytes 1) _root_.Bool.false
#guard !(foreignFromBytesProducerAccepts .native _root_.Bool.false)
#guard !(foreignFromBytesProducerAccepts (.bytes 1) _root_.Bool.true)

/-- error: foreignInv does not accept point values -/
#guard_msgs in
noctium_circuit invalidForeignInverse where
  private point : Secp256k1Point
  output inverse : Secp256k1Point := foreignInv(point)
end

/-- error: foreignAdd requires matching curve and role -/
#guard_msgs in
noctium_circuit mismatchedForeignAdd where
  private left : Secp256k1Base
  private right : Secp256r1Base
  output result : Secp256k1Base := foreignAdd(left, right)
end
