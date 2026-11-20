import Noctium.Frontend

open scoped Noctium

namespace StandardEvents

noctium_circuit spendInputs where
  private active : Bool
  private nullifier : Bytes 32
end

noctium_contract Token where
  entry logSpend uses spendInputs where
    emitEvent(Paused)
    when disclose(active) emitEvent(ShieldedSpend, nullifier := disclose(nullifier))
    emitEvent(Unpaused)
  end
end

end StandardEvents
