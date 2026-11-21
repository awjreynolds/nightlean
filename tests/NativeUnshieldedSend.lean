import Noctium.Frontend

open scoped Noctium

noctium_circuit unshieldedSendInputs where
  public color : Bytes32
  public amount : UInt 128
  public isContract : Bool
  public recipient : Bytes32
end

noctium_contract NativeUnshieldedSend where
  entry send uses unshieldedSendInputs where
    incUnshieldedOutputs(color, amount, true)
    claimUnshieldedCoinSpend(color, amount, true, isContract, recipient)
    readSelf as own
    when boolAnd(isContract, eq(recipient, own)) incUnshieldedInputs(color, amount, true)
  end
end
