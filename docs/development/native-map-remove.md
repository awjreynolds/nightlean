# Native map deletion

`remove escrow[disclose(owner)][disclose(spender)]` removes one entry from
an existing nested map. An absent final key is a no-op. An absent parent map
rejects, matching the pinned ledger VM. Removing a key preserves its siblings
and the other outer-map entries.

Removal accepts scalar and checked composite map values. It does not read the
removed value or require a caller-supplied replacement. Map keys and activity
guards follow the same disclosure checks as insertion and replacement.

The typed `removePath` effect lowers to a `mapRemove` plan operation. For N map
keys, the runtime emits four native VM operations:

1. Index the parent map with the path retained on the stack.
2. Push the final key using its declared alignment.
3. Remove the key with uncached `Rem`.
4. Reinsert the changed parent through the retained path with uncached `Ins(N)`.

Each operation has a separate Impact activity group. A false source guard skips
all four and avoids evaluating the removal path. No ZKIR instruction name is
added. This extends native ledger-state lowering.

`tests/NativeMapRemove.lean` is the source fixture.
`runtime/tests/native_map_remove.rs` is the focused selected-3.2.1 native case.
It checks deletion, repeat deletion, sibling preservation, missing-parent
rejection and guarded inactivity. This slice generates no keys, proofs or
transactions. The focused native case passes in 0.02 seconds.
General state-preservation proofs remain separate work.

The confidential-token port needs this primitive when refunding and replacing
an owner's prior escrow approval.
