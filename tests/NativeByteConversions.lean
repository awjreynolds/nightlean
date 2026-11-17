import Noctium.Frontend

open scoped Noctium

-- Codec outputs deliberately release data. This fixture makes no confidentiality claim.
noctium_circuit byteConversions where
  private native : Native
  private scalar : JubjubScalar
  private point : JubjubPoint
  private fieldRaw : Bytes32
  private pointRaw : Bytes32
  assert eq(fromBytes32(Native, toBytes32(native)), native)
  assert eq(fromBytes32(JubjubScalar, toBytes32(scalar)), scalar)
  assert eq(fromBytes32(JubjubPoint, toBytes32(point)), point)
  output nativeValue : Native := disclose(fromBytes32(Native, fieldRaw))
  output scalarValue : Native := disclose(jubjubScalarToNative(fromBytes32(JubjubScalar, fieldRaw)))
  output x : Native := disclose(jubjubX(fromBytes32(JubjubPoint, pointRaw)))
  output y : Native := disclose(jubjubY(fromBytes32(JubjubPoint, pointRaw)))
end

noctium_circuit discardedPointDecode where
  private pointRaw : Bytes32
  let unused : JubjubPoint := fromBytes32(JubjubPoint, pointRaw)
  output constant : Native := 0
end

noctium_circuit guardedPointDecode where
  private pointRaw : Bytes32
  public enabled : Bool
end

noctium_contract NativeByteConversions where
  cell nativeResult : Native
  cell scalarResult : Native
  cell xResult : Native
  cell yResult : Native
  entry convert uses byteConversions where
    write nativeResult := nativeValue
    write scalarResult := scalarValue
    write xResult := x
    write yResult := y
  end
  entry discard uses discardedPointDecode where
    write nativeResult := constant
  end
  entry guarded uses guardedPointDecode where
    when enabled write xResult := disclose(jubjubX(fromBytes32(JubjubPoint, pointRaw)))
    when enabled write yResult := disclose(jubjubY(fromBytes32(JubjubPoint, pointRaw)))
  end
end
