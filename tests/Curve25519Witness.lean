import Noctium.Frontend
import Noctium.Disclosure

open scoped Noctium

noctium_witness deriveCurve25519Scalar(value : Curve25519Scalar) : Curve25519Scalar
noctium_witness deriveCurve25519Point(value : Curve25519Point) : Curve25519Point

noctium_witness_circuit curve25519WitnessCheck where
  public expectedScalar : Curve25519Scalar
  public expectedPoint : Curve25519Point
  private scalar : Curve25519Scalar
  private point : Curve25519Point
  let returnedScalar : Curve25519Scalar := witness deriveCurve25519Scalar(scalar)
  let returnedPoint : Curve25519Point := witness deriveCurve25519Point(point)
  let scalarResult : Curve25519Scalar := foreignAdd(returnedScalar, curve25519Scalar(1))
  let pointResult : Curve25519Point := foreignAdd(returnedPoint, returnedPoint)
  prove eq(scalarResult, expectedScalar)
  prove eq(pointResult, expectedPoint)
  output scalarMatches : Bool := disclose(eq(scalarResult, expectedScalar))
  output pointMatches : Bool := disclose(eq(pointResult, expectedPoint))
end

noctium_contract Curve25519Witness where
  entry claim uses curve25519WitnessCheck where
    require eq(scalarMatches, true)
    require eq(pointMatches, true)
  end
end
