import Noctium.Frontend

open scoped Noctium

noctium_witness echoScalar(value : JubjubScalar) : JubjubScalar
noctium_witness echoPoint(value : JubjubPoint) : JubjubPoint

noctium_witness_circuit curveCheck where
  private scalar : JubjubScalar
  private point : JubjubPoint
  private expectedScalar : JubjubScalar
  private expectedPoint : JubjubPoint
  let returnedScalar : JubjubScalar := witness echoScalar(scalar)
  let returnedPoint : JubjubPoint := witness echoPoint(point)
  prove eq(returnedScalar, expectedScalar)
  prove eq(returnedPoint, expectedPoint)
  output scalarMatches : Bool := disclose(eq(returnedScalar, expectedScalar))
end

noctium_contract CurveWitness where
  entry claim uses curveCheck where
    require eq(scalarMatches, true)
  end
end
