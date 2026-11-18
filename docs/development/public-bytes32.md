# Packed public Bytes32 inputs

A public Bytes32 input uses one bytes-aligned Push/Popeq pair in the ledger transcript prologue. The application still supplies one canonical 32-byte value. Private Bytes32 inputs keep their existing 32-byte input path. Other byte lengths keep their current encoding.

The native public input contains two bounded scalar fields in FAB order: the final byte first, then the little-endian integer formed from the first 31 bytes. The first field is bounded to 8 bits and the second to 248 bits. Logical byte operations use low31/high order when reconstructing the original value.

Both bounds matter. A single Native-field reduction would lose byte identity. The packed representation preserves every bit, including byte 31, and keeps zero distinct from a byte encoding of the Native modulus.

## Measured artifact change

The same [Bytes32 map source](../../tests/Issue69Bytes32Map.lean) has the following retained and packed artifacts:

| Metric | Retained bytewise input | Packed input |
| --- | ---: | ---: |
| Public prologue VM operations | 64 | 2 |
| Public prologue reads | 32 | 1 |
| Whole fixture VM operations | 84 | 22 |
| Whole fixture reads | 36 | 5 |
| ZKIR instructions | 357 | 173 |
| ZKIR JSON bytes | 36,520 | 15,479 |

These are structural measurements for this fixture. They establish no proving-time, K-value or Compact comparison claim.

## Binding and compatibility

The source input stays typed as Bytes32. Its two public chunk identifiers are reserved compiler names. NativeExpected derives the same aligned pair and the producer requires both range constraints. Source byte operations retain the original order through the existing chunk reconstruction helpers.

The runtime recognizes the packed logical prologue and the retained bytewise prologue separately. Each plan must match its native relation's input names, ordering and bounds. A packed plan paired with a bytewise relation, or the reverse, rejects.

The [native conformance case](../../runtime/tests/public_bytes32.rs) compares both artifacts through the upstream checker and exact ledger state. It covers zero, modulus-sized and full-FF keys, repeated lookup, unchanged private input width, malformed byte values and changed public chunks. Focused control checks cover packed and retained prologue validation.

No new keys, proofs or deployments qualify this optimization. Byte ledger values and public packing for other lengths remain full-goal work. The implementation follows [issue 72](https://github.com/awjreynolds/noctium/issues/72).
