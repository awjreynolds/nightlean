import Noctium.Frontend

open scoped Noctium

-- An inverse determines its nonzero input. These outputs deliberately release arithmetic data.
noctium_circuit inverseValues where
  private denominator : Native
  private scalar : JubjubScalar
  output nativeValue : Native := disclose(inv(denominator))
  output scalarValue : Native := disclose(jubjubScalarToNative(inv(scalar)))
end

noctium_circuit discardedInverse where
  private denominator : Native
  private scalar : JubjubScalar
  let unusedNative : Native := inv(denominator)
  let unusedScalar : JubjubScalar := inv(scalar)
  output constant : Native := 0
end

noctium_circuit guardedInverse where
  private denominator : Native
  private scalar : JubjubScalar
  public enabled : Bool
end

noctium_contract NativeInverse where
  cell nativeResult : Native
  cell scalarResult : Native
  entry invert uses inverseValues where
    write nativeResult := nativeValue
    write scalarResult := scalarValue
  end
  entry discard uses discardedInverse where
    write nativeResult := constant
  end
  entry guarded uses guardedInverse where
    when enabled write nativeResult := disclose(inv(denominator))
    when enabled write scalarResult := disclose(jubjubScalarToNative(inv(scalar)))
  end
end
