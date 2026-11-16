# Native unsigned scalar slice

The Rust evaluator and C ABI implement the scalar rules in `Nightlean/ScalarPolicy.lean`. This extends the existing Native/Bool representation. It adds no Compact runtime or compiler dependency.

Normalized plan types use `UIntRange<N>`, with a canonical decimal exclusive bound `1 <= N <= 2^248`. Runtime values use canonical decimal JSON strings in `[0,N)`. JSON numbers, signed strings, redundant leading zeroes and string booleans reject. The inclusive maximum is `N-1`. The supported source forms UInt width and UIntRange bound normalize before reaching the runtime. User-defined type aliases remain outside this slice.

The new expression schema is:

| Tag | Fields | Rule |
| --- | --- | --- |
| `uint` | `maximum`, `value`, both decimal strings | Validate inclusive maximum and value |
| `uadd` | `left`, `right`, `maximum` | Result maximum equals the sum of operand maxima |
| `usub` | `left`, `right`, `maximum` | Result maximum equals the left maximum, underflow rejects |
| `umul` | `left`, `right`, `maximum` | Result maximum equals the product of operand maxima |
| `cast` | `type`, `value` | Checked scalar conversion |
| `sub` | `left`, `right` | Native field subtraction |

Unsigned arithmetic recomputes the inferred maximum from operand types. A supplied maximum must match exactly. Inferred maxima above `2^248-1` reject even when particular operand values produce a small result. Native arithmetic retains field semantics and requires Native operands. The Lean frontend inserts explicit casts for mixed Native/unsigned arithmetic. Boolean arithmetic requires a cast.

Casts to Bool use zero/nonzero semantics. Casts to an unsigned type validate the actual value against the target maximum, including narrowing. Widening changes the declared type without changing the number. Equality and eager selection require exact scalar types, including the unsigned maximum. Outputs require exact declared types and explicit public visibility.

Unsigned state cells and map schema types use the existing scalar field encoding. Decoding a state cell rechecks its declared range. Nonempty initial maps and reads after writes retain the previous slice's restrictions. The runtime still requires the official circuit checker for compiled constraints and guards.

The C ABI remains version 1. A provider request carries the normalized type in `request.type`, for example `UIntRange<256>`. The response value is a decimal string. Wrong range or representation rejects without consuming the pending request. Native/Bool provider requests retain their existing encoding.

The bounded ZKIR whitelist now includes `neg`, `not`, `constrain_eq`, `constrain_bits` and `less_than`. Bit counts must be integers in 1 through 248. Native ZKIR implements source subtraction through negation and addition. There is no native `sub` instruction. A zero-only range uses `constrain_eq`, and a power-of-two exclusive bound uses `constrain_bits` without an out-of-range comparison constant.

`runtime/tests/unsigned.rs` covers maximum and maximum-plus-one boundaries, malformed inputs, type confusion, inferred-range limits, subtraction underflow, conversions, output visibility and unsigned state cells. Its checked-in fixture comes from `examples/BoundedScalars.lean`. The native checker accepts private values 255 and 255 with public sum 510, then rejects a wrong sum, out-of-range input and nonzero previous cell.

The linked C++ harness also executes this source-generated fixture through typed providers. Reuse the qualified native fixture's parameters/address to prepare both public envelopes:

```sh
python3 runtime/tests/prepare_abi_fixture.py "$QUALIFIED_ARTIFACTS" /tmp/nightlean-abi-public.json
python3 runtime/tests/prepare_abi_fixture.py "$QUALIFIED_ARTIFACTS" /tmp/nightlean-abi-unsigned.json --unsigned-fixture
env -i PATH=/usr/bin:/bin /tmp/nightlean-cpp-smoke /tmp/nightlean-abi-public.json /tmp/nightlean-abi-unsigned.json
```

Build/link commands are in [native-runtime-abi.md](native-runtime-abi.md). The unsigned test supplies both private values from C++, verifies canonical/range/type response rejection, and obtains public result 510 after official checking. The original claim and its invalid/replay checks remain the Native/Bool regression.

This runtime check does not generate a proof or submit a ledger transaction. Issue 33's parent integration separately qualifies the generated relation, key material, prover and local ledger roundtrip. General scalar feature equivalence remains broader than this first unsigned slice.
