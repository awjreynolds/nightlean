# Native memo Lists

Noctium lowers Lists of checked Native-field records directly to the pinned
ledger VM. A node is `Array[Cell(record), tail, Cell(length)]`. The empty value
is `Array[Null, Null, Cell(0u64)]`. Length uses the ledger's eight-byte u64 FAB
alignment. Record fields retain their checked order and Field alignment.

`tests/NativeList.lean` declares a standalone `list inbox : struct Memo {...}`
and a two-key `tree memos : Bytes32 => Bytes32 => List struct Memo {...}`.
The source operations are:

- `reset path` initializes or clears a List. Parent maps need explicit creation.
- `length path as count` binds a UInt64 value.
- `head path as memo` binds the checked record fields, such as `memo_x`.
- `pushFront path := fields(...)` prepends one record.
- `popFront path` removes the first record.

Head and pop reject empty Lists. Read length and guard the operation when an
empty List is valid application input. Pop includes a native length decrement
check before selecting the tail, so the ledger also rejects an empty pop.
The optional presence-plus-default head API remains separate work.

Each List effect emits one guarded native sequence. Each VM opcode retains its
own activity entry, with the same source guard across the sequence. An inactive operation skips
its path lookup and payload evaluation. Inactive head and length reads bind zero
values with the same source guard. Reads after writes use the ordered native
state prefix. Nested paths preserve other owners and spenders. A List permits
at most 13 map keys because prepend needs an additional native insertion level.
The three-slot node shape does not impose a three-element List limit.

Ledger Lists are public state. Ciphertext-shaped records still require explicit
field disclosure at writes. Storing encrypted fields does not by itself prove
correct encryption, key ownership, or a privacy policy. This storage layer
reuses the record schemas needed by the confidential-token memo workload.

The focused source/native example is `tests/NativeList.lean` plus
`runtime/tests/native_list.rs`. It covers prepend order, reads, removal, reset,
separate nested paths, inactive guards, exact storage alignment and rejection
of empty operations and malformed record payloads. The empty-pop rejection also
runs against the emitted native program without host preparation.

The recipes follow the pinned ledger's
[List fragments](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-runtime/vendored/program_fragments.rs#L434-L527)
and [StateValue field encoding](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-state/src/state.rs#L401-L435).
The compiler uses uncached native operations and an explicit nonempty guard for
pop. It does not depend on the Compact compiler or runtime.

This slice covers Native-field record elements. Mixed element types, the full
optional head API, token policy integration and broader preservation proofs
remain open. No new keys, proofs or deployments were generated.
