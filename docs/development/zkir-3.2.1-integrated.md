# Selectable ZKIR 3.2.1 native profile

The profile integration is built from reviewed compiler/runtime commit `41482a1602111ea7d3ede9db343439355c7b2935`. Qualification uses an isolated archive of that commit, not the development worktree. The default 3.2.0 profile and its historical artifacts remain unchanged. The earlier experimental [qualification record](zkir-3.2.1-qualification.md) and its receipts remain separate evidence.

## Select the source target

```sh
noctium compile examples/PrivateClaim.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --output build/claim-321
```

The selector manifest is [midnight-ledger-9-zkir-3.2.1-target.json](../../profiles/midnight-ledger-9-zkir-3.2.1-target.json). The existing similarly named manifest without `-target` remains the historical experiment record. It is not the selector manifest.

The selected profile records release `3.2.1`, source tag `zkir-3.2.1`, revision `7a51b3385bbf4bce3604df87a7c70867c9ab43c0`, declared crate version `3.2.0` and observed CLI banner `midnight-zkir 3.2.0`. The upstream patch did not update its crate/banner. Noctium preserves these distinct identities instead of editing upstream source or inferring the release from its banner.

Both the CLI check and compile passes receive the validated target. The legacy `#nightlean_compile` command still uses 3.2.0. The selected compile command is `#nightlean_compile_target directory profileJson`. Only 3.2.1 plans add `target` and full `targetProfile` fields. Compiler metadata carries the same exact profile. IR language version remains 3.2. The default profile still omits the optional native-source field, preserving its original serialized profile and compiler artifact bytes.

## Select the matching native build

Each Rust build links one supported v3 source revision:

```sh
CARGO_TARGET_DIR=build/runtime-320 cargo build --manifest-path runtime/Cargo.toml --locked
CARGO_TARGET_DIR=build/runtime-321 cargo build --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321
```

Default feature `zkir-320` links revision `446c7fecc6bd41dab99ebe89ab404e9d077d11a9`. Explicit feature `zkir-321` links revision `7a51b3385bbf4bce3604df87a7c70867c9ab43c0`. Both packages declare version 3.2.0, so the source URL/revision identifies the actual dependency. Cargo.lock contains both optional source records. The active dependency graph selects only one v3 implementation. The ledger's separate legacy ZKIR v2 compatibility dependency is unchanged.

Neither feature and both features are compile errors. A 3.2.1 build requires explicitly labeled matching plans. The 3.2.0 build retains legacy unlabeled plans and rejects 3.2.1 labels. The ABI profile string is `midnight-ledger-9-zkir-3.2.1` for the new build. Existing ABI version 1 and scalar encodings remain unchanged. C/C++ hosts link the selected library and submit matching artifact metadata.

The assembler, runtime CLI and verified public artifact consumer validate this selected profile before execution. A manifest's target, profile source pin, compiler metadata, plan metadata, ABI profile and native tool provenance must agree with the linked consumer. A 3.2.0-only consumer rejects a genuine 3.2.1 bundle. Present non-string plan targets reject instead of falling back to legacy handling.

The normalized 3.2.1 native tool provenance retains `requestedVersion: 3.2.1`, `releaseLabel: 3.2.1` and `expectedCliVersion: 3.2.0`, together with the exact source revision and binary/lockfile hashes. The 3.2.0 normalization stays byte-compatible with historical manifests. Key files alone contain no reliable producer-release marker. Matching source/manifest provenance is checked separately from the key/IR correspondence established by actual proof verification.

## Exact-commit qualification

The final qualification stages are:

1. Archive commit 41482a1 into an isolated directory and build its Lean CLI and Rust `zkir-321` consumer.
2. Compile PrivateClaim, BoundedScalars and all adversarial scalar sources through the explicit selector.
3. Generate fresh keys with the pinned clean official 3.2.1 native tool and its verified parameter cache.
4. Assemble public bundles recording compiler revision 41482a1. Verify each trusted manifest digest before reading private configuration or building native transaction intents.
5. Prove and submit the verified native artifacts on the isolated development ledger, compare exact fetched state bytes, reject invalid cases and check replay against the fetched state.

Public bundle manifest digests from this exact compiler commit are:

| Selected entrypoint | Manifest SHA-256 |
| --- | --- |
| PrivateClaim.claim | `963f742b2e4f959685ad1667a31da3b71a56c053af532ebc8801c76d81e8c365` |
| BoundedScalars.apply | `e16984ee8832ea06b6dc9982e72edf9017f9ef9c12b22b9831e95efa5bee4a93` |

The source IR/plan bytes and public bundles carry no witness values. Private execution configuration and intents remain in separate restricted directories. The Node development harness orchestrates the native funding/proof toolkit and checks receipts. Source evaluation, constructor preimage checking, state execution and replay use the matching native Rust consumer, without a Compact dependency.

Final receipt details are recorded in [integrated-profile-evidence.json](../../tests/zkir321/integrated-profile-evidence.json). Earlier development-worktree runs are functional diagnostics, not the source-provenance basis for this qualification.

| Exact-commit workload | Deploy / call heights | Call transaction | Exact state SHA-256 |
| --- | --- | --- | --- |
| PrivateClaim | 2876 / 2879 | `0x417d6079cc70eb368c529d984fdc64bcd6dd02398adf7500f1ae3a52224dc039` | `d03deaed2a47e077412acd4db0fb3069e47cd41d05472eebb3c8182f0c938dc3` |
| BoundedScalars | 2902 / 2930 | `0x71991c0e1e2277bcfb5698ae5cd52492d07acb2baee68cdbcb2bef231f348a8e` | `af3582afe2dfe37f8ffb362286cee7a1e0de035c481e63594b0fde25c609d9cf` |

Both workloads received applied deployment and call receipts. Five claim negatives and two unsigned negatives rejected before submission. Replay rejected against each fetched state, no replay transaction was submitted, and a second fetch returned unchanged bytes. The isolated unsigned receipt watcher initially lacked its client dependency after deployment broadcast. Matching archived package/lock files were checked, installed client dependencies were reused, the existing deployment receipt was recovered, and only the call was resumed. No duplicate deployment was submitted.

## Regression boundaries

The 3.2.0 native suite passed 53 tests and the 3.2.1 suite passed 54, with three external-material tests left opt-in in each default run. The exact-commit scalar and verified-bundle tests were also run explicitly and passed. Actual invalid builds with neither or both profile features reject. Active Cargo trees show the expected single v3 source pin. Linked C++ checks cover the existing Native/Bool claim, unsigned source contract and private-journal host protocol.

The linked native checker runs all ten raw Boolean cases and all 34 source-generated scalar/adversarial cases. Native 3.2.0 intermediate-Jubjub keygen reproduces exit 101. Pinned 3.2.1 keygen succeeds at k10/684 rows, and its linked sizing/checker test succeeds. The independent Boolean fixture generates keys at k9/20 rows. These raw regressions do not introduce source Jubjub or general deserialization support.

Profile qualification remains limited to the selected native scalar/claim workflows and measured backend regressions. It does not qualify every native opcode, source type, curve, public network, mobile binding or full feature equivalence.
