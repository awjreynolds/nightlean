# Sequential cell reads after writes

This note records finite source-to-runtime evidence for ordered cell reads in Noctium entrypoints. The Lean state evaluator applies effects to a tentative `LedgerState` in source order. Native preparation now resolves a later cell read from the onchain VM state after earlier completed mutations.

The implementation is commit `cd4eb2bb0ad57d088c155b11a665487ff8e8da51`. Its complete tracked runtime and Lean source fixture match the independently tested snapshot, including Git executable modes. The implementation adds bounded runtime support. It does not establish a generic source-to-native state-preservation theorem or a ledger deployment claim.

## Runtime behavior

`runtime/src/lib.rs` keeps the full operation order produced by Impact lowering. Each native `Insert` records a completed mutation boundary. When `prepare` reaches an unresolved cell read after a write, `advance_native_state_prefix` runs only the unmaterialized operation suffix through the latest completed `Insert` with `QueryContext::query`. `read_cell` then decodes the value from this native context and preserves the existing canonical Bool and UInt checks.

Each completed suffix runs once. Prefix queries receive the same runtime cost model as final native execution. Reads before the first write use the original context and skip prefix execution. The prefix context supplies values for later reads only. The existing full-program native query, transcript partitioning, transcript execution, and returned successor-state path remain in place.

Map insertion remains supported. Map-value reads remain explicitly rejected by Impact lowering.

## Fixture coverage

`tests/Issue65StateOrdering.lean` checks source execution and emits three entrypoint plans:

- `sequential` reads a Native cell, writes values 1 and 2 with reads after each write, reads an unchanged Native cell after those writes, writes and reads Bool and UInt cells, inserts into a map, then reads the unchanged cell again.
- `failingGuard` writes and reads a cell, then requires a false condition.
- `noncanonicalRead` writes one cell, then reads a Bool cell whose native field encoding is noncanonical.

Native preparation and `noctium_runtime::check` confirm ordered read outputs `0, 1, 2, 9, 1, 255, 9`, the resulting cell values, and one map entry. A changed read value fails native checking. The noncanonical Bool read fails preparation. The failing guard fails native checking while the original input state stays unchanged.

The PrivateClaim regression keeps its reads before its map insertion. The test checks its ordered public transcript values, private transcript values, final cells, and inserted map entry. Existing unsigned tests also pass. These checks exercise the no-prefix path used by programs whose reads precede writes.

## Reproduction

Run from the repository root with Lean 4.35.0:

```sh
lake build
lake env lean tests/Issue65StateOrdering.lean
OUT=$(mktemp -d /private/tmp/noctium-state65.XXXXXX)
lake exe noctium compile tests/Issue65StateOrdering.lean --output "$OUT/issue65-320"
lake exe noctium compile tests/Issue65StateOrdering.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output "$OUT/issue65-321"
lake exe noctium compile examples/PrivateClaim.lean --output "$OUT/private-claim-320"
lake exe noctium compile examples/PrivateClaim.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output "$OUT/private-claim-321"
```

The emitted plans and circuits compare byte-for-byte with the checked-in fixtures. The comparison list and SHA-256 values appear in [the evidence record](../../tests/sequential-state-evidence.json).

The parent runtime qualification ran these locked, offline commands on each selected profile:

```sh
/private/tmp/noctium-cargo/bin/cargo +1.100.0 test --manifest-path runtime/Cargo.toml \
  --locked --offline --test state_ordering --test validation --test unsigned
/private/tmp/noctium-cargo/bin/cargo +1.100.0 test --manifest-path runtime/Cargo.toml \
  --locked --offline --no-default-features --features zkir-321 \
  --test state_ordering --test validation --test unsigned
```

Both runs passed 5 state-ordering tests, 9 validation tests, and 6 unsigned tests. The evidence record binds each run to its parent log hash, source hashes, selected profile, and generated fixture hashes. No ledger submission occurred.
