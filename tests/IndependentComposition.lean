import Noctium.Frontend
open scoped Noctium

noctium_circuit independentCallerInputs where
  public target : Bytes32
  public entryHash : Bytes32
  public commitment : Native
  public credential : Native
  private secret : Native
  assert eq(transientHashNativeVector([secret]), credential)
end

noctium_contract IndependentCaller where
  cell acceptedCredential : Native
  entry claim uses independentCallerInputs where
    read acceptedCredential as expected
    require eq(expected, credential)
    claimContractCall(target, entryHash, commitment)
  end
end

noctium_circuit independentCalleeInputs where
  public credential : Native
  private secret : Native
  private amount : Native
  assert eq(transientHashNativeVector([secret]), credential)
end

noctium_contract IndependentCallee where
  cell acceptedCredential : Native
  cell balance : Native
  counter count
  entry advance uses independentCalleeInputs arguments [amount] where
    read acceptedCredential as expected
    require eq(expected, credential)
    read balance as beforeBalance
    write balance := disclose(add(beforeBalance, amount))
    increment count by 1
  end
end
