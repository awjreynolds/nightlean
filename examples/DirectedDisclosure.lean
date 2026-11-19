import Noctium.Frontend

open scoped Noctium

namespace DirectedDisclosure

noctium_circuit encrypt where
  public recipient : JubjubPoint
  private value : UInt 8
  private nonce : JubjubScalar
  let c1 : JubjubPoint := jubjubMulGenerator(nonce)
  let message : JubjubPoint := jubjubMulGenerator(jubjubScalarFromNative(cast(Native, value)))
  let c2 : JubjubPoint := jubjubAdd(message, jubjubMul(recipient, nonce))
  assert eq(eq(recipient, jubjubFromCoordinates(0, 1)), false)
  assert eq(eq(jubjubScalarToNative(nonce), 0), false)
  output ephemeral : JubjubPoint := disclose(c1)
  output ciphertext : JubjubPoint := disclose(c2)
end

noctium_contract Inbox where
  sealed cell receiver : JubjubPoint
  cell lastEphemeral : JubjubPoint
  cell lastCiphertext : JubjubPoint

  constructor(receiverKey : JubjubPoint) where
    initialize receiver := receiverKey
    initialize lastEphemeral := jubjubFromCoordinates(0, 1)
    initialize lastCiphertext := jubjubFromCoordinates(0, 1)
  end

  entry publish uses encrypt where
    read receiver as authorized
    require eq(recipient, authorized)
    write lastEphemeral := ephemeral
    write lastCiphertext := ciphertext
  end
end

end DirectedDisclosure
