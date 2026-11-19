import Noctium.Frontend

open scoped Noctium

namespace StandardEvents

noctium_circuit spendInputs where
  public active : Bool
  private nullifier : Bytes 32
end

noctium_circuit catalogInputs where
  private commitment : Bytes 32
  public domain : Bytes 32
  private ciphertext : Bytes 512
  public memo : Bytes 256
  public value : UInt 128
end

noctium_contract Token where
  entry logSpend uses spendInputs where
    emitEvent(Paused)
    when active emitEvent(ShieldedSpend, nullifier := disclose(nullifier))
    emitEvent(Unpaused)
  end

  entry logCatalog uses catalogInputs where
    emitEvent(ShieldedSpend, nullifier := disclose(commitment))
    emitEvent(ShieldedReceive, commitment := disclose(commitment), hasCiphertext := true,
      ciphertext := disclose(ciphertext), hasContractAddress := false, contractAddress := domain)
    emitEvent(ShieldedMint, commitment := disclose(commitment), domainSep := domain,
      hasAmount := true, amount := value)
    emitEvent(ShieldedBurn, nullifier := domain, hasAmount := true, amount := value)
    emitEvent(UnshieldedSpend, isUser := true, userKey := disclose(commitment),
      contractAddress := domain, domainSep := domain, tokenType := disclose(commitment), amount := value)
    emitEvent(UnshieldedReceive, isUser := false, userKey := disclose(commitment),
      contractAddress := domain, domainSep := domain, tokenType := disclose(commitment), amount := value)
    emitEvent(UnshieldedMint, domainSep := domain, tokenType := disclose(commitment), amount := value)
    emitEvent(UnshieldedBurn, isUser := true, userKey := disclose(commitment),
      contractAddress := domain, tokenType := disclose(commitment), amount := value)
    emitEvent(Paused)
    emitEvent(Unpaused)
    emitEvent(Misc, payload := memo, name := domain)
  end
end

end StandardEvents
