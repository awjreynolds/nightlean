import Noctium.Backend.Impact
import Noctium.Backend.Zkir
import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium
open Noctium

noctium_circuit curve25519Operations where
  public expectedBase : Curve25519Base
  public expectedRawScalar : Curve25519Scalar
  public expectedPoint : Curve25519Point
  private base : Curve25519Base
  private scalar : Curve25519Scalar
  private point : Curve25519Point
  private rawBytes : Bytes 64
  private decodeGuard : Bool
  let baseResult : Curve25519Base := foreignMul(foreignAdd(base, curve25519Base(2)), foreignInv(base))
  let scalarResult : Curve25519Scalar := foreignAdd(foreignAdd(scalar, scalar), curve25519Scalar(1))
  let pointResult : Curve25519Point := foreignAdd(curveMul(point, scalar), curveMulGenerator(scalar))
  let pointBytes : Bytes 32 := foreignToBytes(pointResult)
  let baseBytes : Bytes 32 := foreignToBytes(base)
  let roundtripPoint : Curve25519Point := foreignFromBytes(Curve25519Point, foreignToBytes(point))
  let identityX : Curve25519Base := curveX(curve25519Identity())
  let identityY : Curve25519Base := curveY(curve25519Identity())
  let rawBase : Curve25519Base := foreignFromBytes(Curve25519Base, rawBytes)
  let rawScalar : Curve25519Scalar := foreignFromBytes(Curve25519Scalar, rawBytes)
  assert eq(baseResult, expectedBase)
  assert eq(rawScalar, expectedRawScalar)
  assert eq(pointResult, expectedPoint)
  assert eq(foreignAdd(point, foreignNeg(point)), curve25519Identity())
  assert eq(foreignSub(pointResult, curveMulGenerator(scalar)), curveMul(point, scalar))
  assert eq(curveFromCoordinates(curveX(point), curveY(point)), point)
  assert eq(curveFromCoordinates(curve25519Base(0), curve25519Base(1)), curve25519Identity())
  assert eq(identityX, curve25519Base(0))
  assert eq(identityY, curve25519Base(1))
  assert eq(foreignFromBytes(Curve25519Point, pointBytes), pointResult)
  assert eq(foreignFromBytes(Curve25519Base, baseBytes), base)
  output baseResultValue : Curve25519Base := disclose(baseResult)
  output scalarResultValue : Curve25519Scalar := disclose(scalarResult)
  output pointResultValue : Curve25519Point := disclose(pointResult)
  output pointBytesValue : Bytes 32 := disclose(pointBytes)
  output baseBytesValue : Bytes 32 := disclose(baseBytes)
  output roundtripPointValue : Curve25519Point := disclose(roundtripPoint)
  output identityXValue : Curve25519Base := disclose(identityX)
  output identityYValue : Curve25519Base := disclose(identityY)
  output rawBaseValue : Curve25519Base := disclose(rawBase)
  output rawScalarValue : Curve25519Scalar := disclose(rawScalar)
end

noctium_contract Curve25519 where
  cell storedPoint : Curve25519Point
  cell guardedPoint : Curve25519Point
  map storedPoints : Native => Curve25519Point
  constructor() where
    initialize storedPoint := curve25519Identity()
    initialize guardedPoint := curve25519Identity()
  end
  entry inspect uses curve25519Operations where
    read storedPoint as initialPointRead
    member storedPoints[999] as missingPointExists
    when eq(missingPointExists, true) read storedPoints[999] as missingPointValue
    write storedPoint := disclose(pointResultValue)
    read storedPoint as storedPointRead
    insert storedPoints[7] := disclose(pointResultValue)
    read storedPoints[7] as mapPointRead
    when disclose(decodeGuard) write guardedPoint := disclose(foreignFromBytes(Curve25519Point, bytes(32, "")))
    read guardedPoint as guardedPointRead
    return baseResult : Curve25519Base := baseResultValue
    return scalarResult : Curve25519Scalar := scalarResultValue
    return pointResult : Curve25519Point := pointResultValue
    return pointBytes : Bytes 32 := pointBytesValue
    return baseBytes : Bytes 32 := baseBytesValue
    return roundtripPoint : Curve25519Point := roundtripPointValue
    return identityX : Curve25519Base := identityXValue
    return identityY : Curve25519Base := identityYValue
    return rawBase : Curve25519Base := rawBaseValue
    return rawScalar : Curve25519Scalar := rawScalarValue
    return initialPoint : Curve25519Point := disclose(initialPointRead)
    return storedPointResult : Curve25519Point := disclose(storedPointRead)
    return mapPointResult : Curve25519Point := disclose(mapPointRead)
    return missingPointResult : Curve25519Point := disclose(missingPointValue)
    return guardedPointBytes : Bytes 32 := disclose(foreignToBytes(guardedPointRead))
  end
end

#guard Foreign.Kind.sourceName (.base .curve25519) == "Curve25519Base"
#guard Foreign.Kind.sourceName (.scalar .curve25519) == "Curve25519Scalar"
#guard Foreign.Kind.sourceName (.point .curve25519) == "Curve25519Point"
#guard Foreign.Kind.byteLength (.point .curve25519) == 32
