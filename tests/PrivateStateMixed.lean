import Noctium.Frontend

open scoped Noctium

namespace PrivateStateMixed

noctium_private_state Wallet where
  cell saved : UInt 8
  cell enabled : Bool
end

noctium_witness_circuit consume where
  public expected : UInt 8
  read private Wallet.saved as previous
  read private Wallet.enabled as enabled
  prove enabled
  prove eq(expected, add(previous, uint(1)))
  stage Wallet.saved := expected
  stage Wallet.enabled := false
end

noctium_contract Meter where
  cell count : UInt 8
  entry advance uses consume where
    write count := expected
  end
end

end PrivateStateMixed
