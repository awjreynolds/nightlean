import Noctium.Frontend

open scoped Noctium

namespace PrivateStateMixed

private def receiptWire : Noctium.Helpers.Wire.Codec := {
  payload := .structure "MeterReceipt"
  frameBytes := 2
  composites := {structures := [{id := "MeterReceipt", fields := [
    {name := "amount", type := .scalar (.uint 255)},
    {name := "okay", type := .scalar .bool}
  ]}]}
}

noctium_private_state Wallet where
  cell saved : UInt 8
  cell enabled : Bool
  cell secret : JubjubScalar
  cell recipient : JubjubPoint
  cell receipt : Payload receiptWire
end

noctium_witness_circuit consume using receiptWire where
  public expected : UInt 8
  private replacement : JubjubScalar
  read private Wallet.saved as previous
  read private Wallet.enabled as enabled
  read private Wallet.secret as secret
  read private Wallet.recipient as recipient
  read private Wallet.receipt as receipt
  prove enabled
  prove eq(expected, add(previous, uint(1)))
  prove eq(jubjubMulGenerator(secret), recipient)
  prove eq(field(receipt, amount), expected)
  prove field(receipt, okay)
  stage Wallet.saved := expected
  stage Wallet.enabled := false
  stage Wallet.secret := replacement
  stage Wallet.recipient := jubjubMulGenerator(replacement)
  output approved : Bool := disclose(field(receipt, okay))
  output units : UInt 8 := expected
end

noctium_contract Meter where
  cell count : UInt 8
  entry advance uses consume where
    write count := units
    return accepted : Bool := approved
  end
end

end PrivateStateMixed
