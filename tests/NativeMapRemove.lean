import Noctium.Frontend

open scoped Noctium

noctium_circuit mapRemoveInputs where
  public owner : Bytes32
  public spender : Bytes32
  public enabled : Bool
end

noctium_contract NativeMapRemove where
  tree escrow : Bytes32 => Bytes32 => struct EscrowRecord {
    x : Native
    y : Native
  }
  entry «remove» uses mapRemoveInputs where
    when enabled remove escrow[owner][spender]
  end
end
