import Noctium.Frontend

open scoped Noctium

noctium_circuit scalarBoundary where
  private raw : Native
  let scalar : JubjubScalar := jubjubScalarFromNative(raw)
  let point : JubjubPoint := jubjubMulGenerator(scalar)
  output reduced : Native := disclose(jubjubScalarToNative(scalar))
  output pointX : Native := disclose(jubjubX(point))
  output pointY : Native := disclose(jubjubY(point))
end

noctium_contract JubjubScalarBoundary where
  cell reducedCell : Native
  cell pointXCell : Native
  cell pointYCell : Native
  entry multiply uses scalarBoundary where
    write reducedCell := reduced
    write pointXCell := pointX
    write pointYCell := pointY
  end
end
