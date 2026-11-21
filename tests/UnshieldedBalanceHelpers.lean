import Noctium.Frontend

open scoped Noctium

noctium_circuit unshieldedBalanceInputs where
  public color : Bytes32
  public limit : UInt 128
  public enabled : Bool
end

noctium_contract UnshieldedBalanceHelpers where
  entry inspect uses unshieldedBalanceInputs where
    tokenBalance(color, true) as amount
    when enabled tokenBalanceLt(color, true, limit) as below
    when enabled tokenBalanceGt(color, true, limit) as above
    return exactAmount : UInt 128 := amount
    return belowLimit : Bool := below
    return atLeastLimit : Bool := select(enabled, boolXor(below, true), false)
    return aboveLimit : Bool := above
    return atMostLimit : Bool := select(enabled, boolXor(above, true), false)
  end
end
