# Fixed byte values

Use `Bytes n` for a byte string with a compile-time length from 0 through 1024.
The limit reuses the compiler's existing fixed-vector resource bound. `Bytes32`
remains an alias for the 32-byte source type, with its existing wire encoding.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit combine where
  private left : Bytes 31
  private right : Bytes 33
  let joined : Bytes 64 := concatBytes(left, right)
  output first : UInt 8 := disclose(byteAt(joined, 0))
end
```

`reverseBytes(value)` preserves the length. `sliceBytes(value, start, stop)` uses
constant bounds, includes `start` and excludes `stop`. Bounds must satisfy
`start <= stop <= length`. `concatBytes(left, right)` returns the sum of the two
lengths, subject to the same resource limit. `eq(left, right)` compares
equal-length byte values through their checked chunks. `bytes(n, "text")` encodes UTF-8
and pads on the right with zero bytes. Selection requires matching lengths.
Private inputs keep their private origins through each operation. Publishing
a derived value requires an explicit `disclose` at the public output or return.

The host token is `Bytes<n>` and its value is
`{"kind":"bytes","values":[0,1,2]}`. The array must contain exactly the declared
number of integer octets. The SDK rejects malformed lengths and non-byte values.
Rust retains `ScalarType::Bytes32` for 32 bytes and uses `ScalarType::Bytes(n)`
for other supported lengths. Existing source witness and private-state transport
carry the same logical value before expansion to checked Native byte leaves.

Native byte instructions use 31-byte field chunks in low-to-high order. Ledger
output commitments reverse the chunk order through the pinned FAB alignment.
Typed entrypoint results preserve the logical byte value in the host and commit
the corresponding fields in the circuit. A final partial chunk receives its
exact range bound.

The pinned native ZKIR type excludes zero-length bytes. Source `Bytes 0` has one
possible value and no native fields. Empty operations preserve operand evaluation,
assertions and failures while omitting an unsupported native zero-byte value.
Zero-byte equality and unused partial byte bindings also preserve evaluation.

[The source fixture](../../tests/NativeBytes.lean) and
[focused native case](../../runtime/tests/native_bytes.rs) cover chunk boundaries,
selection, typed returns, invalid lengths and output binding. A zero-field return
still rejects a false private assertion. The existing Bytes32 reversal fixture's
circuit and plan remain equal to their retained JSON objects.

These are source and native-checker results on the selected 3.2.1 profile. No new
keys, proofs or deployment were created for this feature. General byte ledger cells
and non-Bytes32 map keys remain gated. Other native byte operations and full
overload, proof and SDK qualification remain part of the wider capability goal.
