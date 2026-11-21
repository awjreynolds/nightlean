import Noctium.Frontend

open scoped Noctium

namespace NoctiumExamples

noctium_private_state Wallet where
  cell saved : UInt 8
end

noctium_witness nextValue(previous : UInt 8) : UInt 8
noctium_witness nextValueAfterCheckpoint(previous : UInt 8) : UInt 8

noctium_witness_circuit advanceOnce where
  public expected : UInt 8
  read private Wallet.saved as previous
  let next : UInt 8 := witness nextValue(previous)
  prove eq(next, cast(UInt 8, add(previous, uint(1))))
  stage Wallet.saved := next
  output nextCount : UInt 8 := expected
end

noctium_witness_circuit advanceAfterCheckpoint where
  public expected : UInt 8
  read private Wallet.saved as previous
  let next : UInt 8 := witness nextValueAfterCheckpoint(previous)
  prove eq(next, cast(UInt 8, add(previous, uint(2))))
  stage Wallet.saved := next
  output nextCount : UInt 8 := expected
end

noctium_contract TypedMultiEntryWitness where
  cell count : UInt 8
  entry advance uses advanceOnce where
    read count as current
    require eq(add(current, uint(1)), expected)
    write count := nextCount
  end
  entry advanceAgain uses advanceAfterCheckpoint where
    read count as current
    require eq(add(current, uint(2)), expected)
    write count := nextCount
  end
end

end NoctiumExamples
