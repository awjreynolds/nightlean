import Noctium.Frontend

open scoped Noctium

noctium_circuit opaqueInput where
  private secret : Bytes32
  private scalar : JubjubScalar
  public enabled : Bool
end

noctium_contract NativeOpaqueReturns where
  cell marker : Native
  entry compute uses opaqueInput where
    write marker := 7
    read marker as observed
    return digest : Bytes32 := disclose(persistentHash32(secret))
    return scalarValue : JubjubScalar := disclose(scalar)
    return pointValue : JubjubPoint := disclose(jubjubMulGenerator(scalar))
    return markerValue : Native := observed
  end
end
