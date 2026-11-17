# Generic ledger state checker fixture

These plans and relations come from `tests/Issue66GenericState.lean` and
`tests/Issue66OutputBinding.lean`. The sources cover Native, Bool and UInt 5 cells,
an untouched cell, two typed maps and a computed output used by a ledger write.
`source-manifest.json` records the source and artifact hashes for both profiles.
The runtime test suite checks those hashes alongside the retained bytes.

Run the selected upstream native checker with either profile:

```sh
cargo test --manifest-path runtime/Cargo.toml --no-default-features --features zkir-320 --test generic_state
cargo test --manifest-path runtime/Cargo.toml --no-default-features --features zkir-321 --test generic_state
```

Regenerate into separate output directories, compare the emitted `.zkir` and
`.impact.json` files, then refresh the manifest hashes after a source change:

```sh
lake exe noctium compile tests/Issue66GenericState.lean --target profiles/midnight-ledger-9.json --output /tmp/noctium-generic-state-320
lake exe noctium compile tests/Issue66GenericState.lean --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --output /tmp/noctium-generic-state-321
lake exe noctium compile tests/Issue66OutputBinding.lean --target profiles/midnight-ledger-9.json --output /tmp/noctium-output-state-320
lake exe noctium compile tests/Issue66OutputBinding.lean --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --output /tmp/noctium-output-state-321
```

The checks cover native preparation, exact successor values, UInt constraints
and rejection of altered slots, map keys, values, operation order, read values
and absence guards. The output fixture also rejects changes to its public input
and later read binding. The tests do not generate proofs or submit ledger
transactions.
