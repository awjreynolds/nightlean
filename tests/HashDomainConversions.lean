import Noctium.Frontend

open scoped Noctium

noctium_circuit hashDomainInputs where
  private digest : Bytes32
  private field : Native
end

noctium_contract HashDomainConversions where
  entry inspect uses hashDomainInputs where
    return truncated : Native := disclose(degradeToNative(digest))
    return encoded : Bytes32 := disclose(upgradeFromNative(field))
  end
end
