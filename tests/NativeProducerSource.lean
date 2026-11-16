import Nightlean.Frontend
open scoped Nightlean

nightlean_circuit publicBoolRoundTrip where
  public flag : Bool
  output result : Bool := flag
end

nightlean_contract PublicBoolCell where
  cell enabled : Bool
  entry apply uses publicBoolRoundTrip where
    read enabled as old
    require eq(old, flag)
    write enabled := flag
  end
end
