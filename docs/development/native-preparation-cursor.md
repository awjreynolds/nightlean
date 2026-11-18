# Resumable native preparation

`PreparationCursor` exposes the existing checked native executor one plan instruction at a time. A host reads ledger data before supplying a private input needed by a later operation. The cursor owns the frozen plan, ledger parameters, address, starting state and ordered native prefix. It uses Midnight's `QueryContext` and the same read-after-write machinery as complete preparation.

The ordinary `prepare` function drives this cursor to completion. There is one ledger executor.

## API and input ownership

- `PreparationCursor::new` requires all public circuit inputs. Private inputs may arrive later. Every declared type is checked before an input request.
- `step` returns `Operation`, `PendingInputs` or `Complete`. Missing private operands pause before their operation executes.
- A read event includes its name, activity flag and only that read's produced bindings. It exposes no full private environment.
- `supply_inputs` checks the entire batch before committing. Unknown names, incorrect types and replacement of a bound value reject.
- `finish` consumes a complete cursor and creates the transcript, predicted state, returns and proof preimage. It rejects incomplete or poisoned cursors.

Fatal step errors poison further execution. Invalid input batches leave accepted inputs unchanged, allowing a corrected batch. The starting state stays immutable. No chain update or private-journal commit occurs during preparation.

Circuit outputs become available as their private dependencies arrive. Complete-input callers use the direct operation path, avoiding speculative operand evaluation. Source instructions retain their native activity groups, mutation boundaries and canonical inactive reads.

## Focused case

The [Lean contract](../../tests/NativePreparationCursor.lean) reads `beforeBalance`, uses private `delta` in a disclosed write, reads `afterBalance`, constrains the public expected result and returns the resulting balance.

The [Rust case](../../runtime/tests/preparation_cursor.rs) begins with balance 3 and expected result 10. It receives the ledger read before the private-input request. The host computes `delta = beforeBalance + 4`, supplies 7, resumes, and observes balance 10. The pinned 3.2.1 checker accepts the resulting relation and transcript. Essential negative cases cover incomplete finish, unknown/type-invalid/replacement input batches, and a malformed native instruction poisoning the cursor.

The current structured-map scenario also passes through the same executor. Only the circuit and ledger plan consumed by these tests are retained as fixtures.

## Integration boundary

The Rust `WitnessExecution` owner now coordinates source Sessions with this cursor for [structured state-dependent typed witnesses](structured-cells.md#state-dependent-typed-witnesses). Internal callbacks bind to native read/write boundaries. External providers retain the existing typed interface, and private staging retains the existing journal owner. Direct cursor users still supply their own private-input scheduling. Portable bindings and broader state layouts need separate qualification.

A completed preimage still needs `check` against the native circuit. Preparation does not prove circuit satisfaction or submit a transaction. No new keys, proofs, deployment, C ABI, web/mobile binding or general preservation theorem accompanies this interface.

Implementation revision: `2b9ff0a30c72fa347fbc0dd5088c260befe7b697`. The source export and two cursor cases pass. The current structured-map case passes in the same focused run. The shared build directory is 1.2 GiB. No additional artifact cache was created.
