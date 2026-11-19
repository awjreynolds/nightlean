import Noctium.Frontend

open scoped Noctium

namespace PrivateStateMixed

noctium_private_state Wallet where
  cell saved : UInt 8
  cell enabled : Bool
  cell secret : JubjubScalar
  cell recipient : JubjubPoint
end

noctium_witness_circuit consume where
  public expected : UInt 8
  private replacement : JubjubScalar
  read private Wallet.saved as previous
  read private Wallet.enabled as enabled
  read private Wallet.secret as secret
  read private Wallet.recipient as recipient
  prove enabled
  prove eq(expected, add(previous, uint(1)))
  prove eq(jubjubMulGenerator(secret), recipient)
  stage Wallet.saved := expected
  stage Wallet.enabled := false
  stage Wallet.secret := replacement
  stage Wallet.recipient := jubjubMulGenerator(replacement)
end

noctium_contract Meter where
  cell count : UInt 8
  entry advance uses consume where
    write count := expected
  end
end

end PrivateStateMixed
