# Native Counter storage and operations

Noctium Counter state uses the pinned ledger's `Cell(u64)` encoding. Its FAB
alignment is one eight-byte atom, not the Field alignment used by ordinary
`UInt 64` cells. Source values read from counters retain the UInt64 range.

The source forms are `counter total`, `tree epochs : Bytes32 => Counter`, and
`tree epochs : Bytes32 => Bytes32 => Counter`. Existing `read ... as` binds the
value. `increment ... by N` and `decrement ... by N` take a public compile-time
u32 amount. `reset ...` writes zero. Missing parent maps require explicit
initialization. A reset initializes an absent counter leaf or replaces an
existing value. Contracts decide whether to expose reset to callers.

Updates use native `Idx(push_path)`, `Addi` or `Subi`, then `Ins`. They do not
bind the previous value as a circuit read unless the source requests a read.
The native VM rejects u64 overflow and underflow. Guards cover every operation
in the selected update sequence, including indexing into an absent path.

`tests/NativeCounter.lean` and `runtime/tests/native_counter.rs` provide the
focused source/native example. It exercises standalone and nested counters,
reads after updates, reset, inactive guards, checked arithmetic and rejection
of field-aligned state supplied as a Counter. The fixture exposes test-only
update/reset entrypoints and establishes no token authorization policy.

The pinned recipes are
[Counter operations](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-runtime/vendored/program_fragments.rs#L158-L217).
Counter uses eight-byte alignment in
[FAB alignments](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/base-crypto/src/fab/alignments.rs#L73-L81).
These source operations add ledger VM support, not new ZKIR instruction names.
Counter comparison helpers and full token integration remain open.
[Native-field memo Lists](native-lists.md) have a separate source/native example.
No new keys, proofs or deployments were generated for this slice.
