import Noctium.Frontend
open scoped Noctium

noctium_circuit authorizedRelease where
  private secret : UInt 8
  public expected : UInt 8
  assert eq(secret, expected)
  output released : UInt 8 := disclose(secret)
end

noctium_circuit authorizedPredicate where
  private flag : Bool
  output selected : Native := select(disclose(flag), 1, 0)
end
