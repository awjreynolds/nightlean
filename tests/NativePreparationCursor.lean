import Noctium.Frontend

open scoped Noctium

noctium_circuit cursorInputs where
  public expected : Native
  private delta : Native
end

noctium_contract NativePreparationCursor where
  cell balance : Native
  entry advance uses cursorInputs where
    read balance as beforeBalance
    write balance := disclose(add(beforeBalance, delta))
    read balance as afterBalance
    require eq(afterBalance, expected)
    return observed : Native := afterBalance
  end
end
