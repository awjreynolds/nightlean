import Noctium.Frontend
open scoped Noctium

/- A private cache belongs to the wallet. It is not replicated ledger state.
The callback result is untrusted until the circuit checks it. Both prove
statements reveal `next` and `previous` on success, so this example makes no
confidentiality claim for counter values. The staged cache write commits only
after verified finality and the wallet's compare-and-swap check. -/
namespace NoctiumExamples

noctium_private_state Wallet where
  cell saved : UInt 8
end

noctium_witness nextValue(previous : UInt 8) : UInt 8

noctium_witness_circuit advance where
  public expected : UInt 8
  read private Wallet.saved as previous
  let next : UInt 8 := witness nextValue(previous)
  prove eq(next, cast(UInt 8, add(previous, uint(1))))
  prove eq(next, expected)
  stage Wallet.saved := next
  output nextCount : UInt 8 := expected
end

noctium_contract PrivateStateCounter where
  cell count : UInt 8
  entry advance uses advance where
    write count := nextCount
  end
end

end NoctiumExamples
