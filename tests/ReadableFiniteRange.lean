import Noctium.Frontend

open scoped Noctium

noctium_private_state RangeWallet where
  cell last : Native
end

noctium_witness rangeStep(index : Native, previous : Native) : Native
noctium_witness rangeObserve(index : Native) : Unit

noctium_witness_circuit readableRange where
  public expected : Native
  for i in 1 ..< 3 do
    read private RangeWallet.last as previous
    let next : Native := witness rangeStep(i, previous)
    prove eq(next, add(previous, i))
    stage RangeWallet.last := next
    for j in 0 ..< 1 do
      witness rangeObserve(add(i, j))
    end
  end
  for skipped in 0 ..< 0 do
    witness rangeObserve(skipped)
  end
  read private RangeWallet.last as finalValue
  prove eq(finalValue, expected)
  output checked : Native := expected
end

noctium_contract ReadableFiniteRange where
  cell total : Native
  entry update uses readableRange where
    write total := checked
    return result : Native := checked
  end
end

/-- error: unknown readable witness value 'i' -/
#guard_msgs in
noctium_witness_circuit escapedIndex where
  for i in 0 ..< 1 do
    prove eq(i, 0)
  end
  output escaped : Native := i
end
