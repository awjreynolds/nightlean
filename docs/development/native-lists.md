# Native memo Lists

Noctium lowers Lists of checked ledger records directly to the pinned
ledger VM. A node is `Array[Cell(record), tail, Cell(length)]`. The empty value
is `Array[Null, Null, Cell(0u64)]`. Length uses the ledger's eight-byte u64 FAB
alignment. Record fields retain their declared order and storage types.
A `Native` field occupies one Field atom, a `Bytes32` field one 32-byte atom,
and a `JubjubPoint` field two Field atoms holding the checked x/y coordinates.

`tests/NativeList.lean` declares a standalone `list inbox : struct Memo {...}`
and a two-key `tree memos : Bytes32 => Bytes32 => List struct Memo {...}`.
The source operations are:

- `reset path` initializes or clears a List. Parent maps need explicit creation.
- `length path as count` binds a UInt64 value.
- `head path as memo` binds the checked record fields, such as `memo_x`.
- `headOrDefault path as (present, memo)` binds a Bool and the same record fields. An empty List returns `false` with typed defaults. Every present record returns `true`.
- `pushFront path := fields(...)` prepends one record.
- `popFront path` removes the first record.

Strict `head` and `popFront` reject empty Lists. Pop includes a native length decrement check before selecting the tail. `headOrDefault` reads the native length and guards the head read with the nonempty result. Noctium binds both reads to the ordered ledger state. An inactive statement returns `false` and typed defaults without looking up its path. A missing active path still rejects.

Each List effect emits one guarded native sequence. Each VM opcode retains its
own activity entry, with the same source guard across the sequence. An inactive operation skips
its path lookup and payload evaluation. Inactive head reads bind zero for
`Native` and `Bytes32` and the identity `(0, 1)` for `JubjubPoint`. An inactive
length read binds zero. Reads after writes use the ordered native
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

[OptionalListHead.lean](../../tests/OptionalListHead.lean) checks the optional form on standalone and nested paths. [MixedLedgerRecord.lean](../../tests/MixedLedgerRecord.lean) uses the same memo shape in map cells and List nodes. `fields(...)` takes one typed expression per declared field. Reads bind names such as `memo_payload` and `memo_ephemeral` with their declared types.
