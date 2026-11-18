import Noctium.Frontend

open scoped Noctium

noctium_circuit issue43PrivateOnly where
  private enabled : Bool
end

noctium_contract Issue43EmptyActivity where
  cell current : Native
  map allowances : Native => Native
  entry apply uses issue43PrivateOnly where
    when disclose(enabled) write current := 21
    when disclose(enabled) insert allowances[7] := 9
  end
end
