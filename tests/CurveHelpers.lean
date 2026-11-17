import Noctium.Frontend

open scoped Noctium

noctium_witness secret() : Native
noctium_witness randomness() : Native
noctium_witness plaintext() : UInt 128

noctium_witness_circuit encrypt where
  public recipient : JubjubPoint
  let secretField : Native := witness secret()
  let randomnessField : Native := witness randomness()
  let plaintextField : UInt 128 := witness plaintext()
  let secretScalar : JubjubScalar := jubjubScalarFromNative(secretField)
  let randomnessScalar : JubjubScalar := jubjubScalarFromNative(randomnessField)
  let plaintextScalar : JubjubScalar := jubjubScalarFromNative(cast(Native, plaintextField))
  prove eq(jubjubMulGenerator(secretScalar), recipient)
  prove eq(jubjubScalarToNative(secretScalar), secretField)
  prove eq(eq(jubjubScalarToNative(secretScalar), 0), false)
  prove eq(eq(jubjubScalarToNative(randomnessScalar), 0), false)
  prove eq(eq(recipient, jubjubFromCoordinates(0, 1)), false)
  let reconstructed : JubjubPoint := jubjubFromCoordinates(jubjubX(recipient), jubjubY(recipient))
  prove eq(reconstructed, recipient)
  let c1 : JubjubPoint := jubjubMulGenerator(randomnessScalar)
  let messagePoint : JubjubPoint := jubjubMulGenerator(plaintextScalar)
  let c2 : JubjubPoint := jubjubAdd(messagePoint, jubjubMul(recipient, randomnessScalar))
  let decrypted : JubjubPoint := jubjubAdd(c2, jubjubNeg(jubjubMul(c1, secretScalar)))
  prove eq(decrypted, messagePoint)
  output c1x : Native := disclose(jubjubX(c1))
  output c1y : Native := disclose(jubjubY(c1))
  output c2x : Native := disclose(jubjubX(c2))
  output c2y : Native := disclose(jubjubY(c2))
end

noctium_contract CurveHelpers where
  cell c1x : Native
  cell c1y : Native
  cell c2x : Native
  cell c2y : Native
  entry encrypt uses encrypt where
    write c1x := result.c1x
    write c1y := result.c1y
    write c2x := result.c2x
    write c2y := result.c2y
  end
end
