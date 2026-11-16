# Native private artifact assembler

`nightlean-assemble` builds unbalanced deployment and call intents directly in Rust. It consumes Lean compiler outputs and the pinned native Midnight key/ledger formats. No JavaScript evaluator, Node subprocess, proof service or network call participates in assembly.

The assembler emits the same directory layout used by the native toolkit qualification flow. These are private execution artifacts. `call-intent.bin`, `constructor-preimage.bin` and `runtime-config.json` contain witness material and do not belong in a public compiler bundle.

## Verified bundle invocation

The high-level path verifies a public bundle against a trusted manifest digest before opening private configuration:

```sh
cargo build --manifest-path runtime/Cargo.toml --locked --bin nightlean-assemble
runtime/target/debug/nightlean-assemble \
  --bundle PUBLIC_BUNDLE_DIRECTORY --manifest-sha256 TRUSTED_MANIFEST_SHA256 \
  --config PRIVATE_CONFIG.json --ttl-unix UNIX_SECONDS NEW_PRIVATE_DIRECTORY
```

The trusted digest must come from outside the selected bundle. Computing a new digest from a changed bundle does not authenticate its original contents. Public bundle paths must satisfy the artifact verifier's canonical-path and no-symlink rules. Verification checks every selected public payload, profile, pin and metadata association before the CLI reads private configuration or executes the plan.

Rust callers first use `artifacts::verify(directory, Some(trusted_digest))`, then pass the resulting `VerifiedBundle` to `assembly::assemble_verified(&bundle, private_config, ttl_unix, output)`. This consumer obtains its plan, circuit, keys and ledger parameters exclusively through retained `bundle.file(Role)` bytes. It does not reopen public paths. Removing or modifying the directory after verification does not change execution inputs. A caller who chooses `verify(directory, None)` has checked integrity without external authentication. The Rust consumer does not invent an authentication claim for this choice.

## Explicit trusted input invocation

The existing lower-level interface remains available for callers who already control and trust every selected input:

```sh
cargo build --manifest-path runtime/Cargo.toml --locked --bin nightlean-assemble
runtime/target/debug/nightlean-assemble \
  SOURCE_PLAN.json ENTRYPOINT.zkir KEY.prover KEY.verifier NEW_PRIVATE_DIRECTORY \
  --ledger-params LEDGER.params --config PRIVATE_CONFIG.json --ttl-unix UNIX_SECONDS
```

The binary resides under `CARGO_TARGET_DIR/debug` when an alternate build directory is selected. All input paths and the expiry timestamp are explicit. `--ttl-unix` is an absolute, positive Unix timestamp in seconds. The host chooses a suitable expiry from its network context. The assembler does not read ambient time or infer an expiry.

The configuration uses the existing native runtime shape:

```json
{"inputs":{"left":"255","right":"255","expected":"510"},"state":{"total":"0"}}
```

This example corresponds to `examples/BoundedScalars.lean`. Unsigned values use canonical decimal strings and enforce their declared bounds. Optional `negativeCases` are retained for subsequent native CLI qualification. They do not enter the assembled call.

## Native transaction path

The assembler decodes the official ledger parameters, native ZKIR and tagged prover/verifier keys. It initializes the key encodings and checks the prover domain size against the circuit. Supplied keys must come from a trusted pinned key-generation step. Parsing and domain-size checks do not establish cryptographic correspondence between a prover key, verifier key and relation. The summary records `keyPairAssociationVerified: false`. Proof generation and verification supply the later integration evidence.

The initial contract includes the configured native state, the supplied verifier key at the selected entrypoint and the existing empty maintenance authority with threshold 1. This matches the earlier qualification fixture's fixed authority. The assembler does not provision upgrade keys.

`ContractDeploy::new` obtains a fresh deployment nonce from the operating system's cryptographic random source. Each `Intent::empty` also obtains a fresh binding commitment through the official constructor. The call uses fresh nonzero field randomness from the same source for its communication commitment.

The existing `prepare` function still provides bounded expression evaluation, typed private fields and the materialized Impact program. Its diagnostic zero-randomness preimage is not used as the transaction preimage. The assembler creates a new `PreTranscript` containing the real communication commitment, repartitions with the supplied ledger parameters, executes those real transcripts and builds a `ContractCallPrototype`.

The official `Intent::add_call::<ProofPreimage>` constructor produces the call's embedded preimage. The assembler checks this exact preimage against native ZKIR, verifies the communication commitment/randomness pair and checks activity metadata. It serializes and deserializes both intents and both state snapshots, requires unchanged serialization bytes, then checks the deserialized call preimage again. Native binding-input placeholders remain under the official constructor/proving lifecycle.

The predicted state comes from executing the real partitioned transcripts. The assembler does not derive the final state by editing a serialized state cell manually.

## Output and privacy

The output parent directory must already exist. The selected output directory must be new. Existing files or directories reject. Validation and native checking complete before the directory is created. On Unix, the new directory and its `keys`/`zkir` children receive mode 0700. Files use exclusive creation with mode 0600. A write failure triggers cleanup of the newly created staging directory. The summary is written last. An interrupted process might leave an incomplete private directory, which must not be treated as a completed assembly.

| Path | Contents |
| --- | --- |
| `keys/ENTRY.prover`, `keys/ENTRY.verifier` | Supplied native key bytes |
| `zkir/ENTRY.zkir`, `zkir/ENTRY.bzkir` | Supplied JSON IR and official tagged binary IR |
| `source-plan.json`, `runtime-config.json`, `ledger.params` | Exact supplied execution inputs |
| `initial-state.bin`, `predicted-state.bin` | Official tagged native contract states |
| `deploy-intent.bin`, `call-intent.bin` | Private, unbalanced official intents |
| `constructor-preimage.bin` | Exact checked preimage from the assembled call |
| `native-contract.json` | Public qualification summary |

The stdout summary contains the contract address, public artifact/state digests, operation counts, expiry, source revisions and qualification flags. It omits witness values and private configuration digests. Private configuration parse errors retain numeric locations and discard value-bearing parser causes, including under full Rust error-chain formatting. The constructor check is recorded separately from proof generation and ledger acceptance. This tool does neither. A native toolkit step supplies fees, proving, signing and submission later.

The current bound is one call with no explicit circuit input/output payload beyond the compiler-owned transcript representation. Native state-map initialization and reads-after-writes retain the evaluator's existing restrictions. The assembler targets the pinned ledger revision and ZKIR 3.2.0 profile. It does not qualify another prover release by changing a label.

## Verification

Focused unit tests check real constructor preimage validation, fresh addresses and communication randomness across runs, intent serialization roundtrips, wrong-sum rejection, private output permissions, rollback and exclusive creation. A real-key run of the final source-generated unsigned sample used native k8 keys, eight guaranteed operations, no fallible operations and a predicted state SHA-256 of `af3582afe2dfe37f8ffb362286cee7a1e0de035c481e63594b0fde25c609d9cf`.

The real-key executable ran with `PATH=/usr/bin:/bin`. A second run produced a different address and call intent with the same predicted state. Wrong-sum input rejected without creating an output directory or echoing witness values. Reusing an existing destination rejected and preserved its bytes. The original Native/Bool claim and linked unsigned provider harness remain regression checks.

The native CLI replay check now runs both `prepare` and the official circuit checker. Some source state guards, including the unsigned sample's initially-zero cell, reject in circuit checking rather than Impact materialization alone. This prevents the CLI from misclassifying a guard-protected replay.

For a state fetched from the ledger, use:

```sh
nightlean-runtime PRIVATE_ARTIFACT_DIRECTORY --check-state FETCHED_STATE.bin --expect-rejection
```

This mode decodes the supplied `ContractState`, then requires execution or official checking to reject against its data. It returns public JSON containing `rejected: true`, the supplied state digest and an unchanged-state check. An accepted execution exits unsuccessfully, as do file, parse, trailing-byte and input-schema failures. The mode does not reconstruct `config.state` or load the golden initial/predicted state files. The `supplied_state` integration test exercises these distinctions through the executable.

The original private one-time claim also passed real-key native assembly with 21 guaranteed operations, k9, no fallible operations and predicted state SHA-256 `d03deaed2a47e077412acd4db0fb3069e47cd41d05472eebb3c8182f0c938dc3`. Its reassembled directory passed the native runtime's five invalid cases and replay check, with no Node invocation or additional deployment.

The `verified_assembly` real-key qualification test is opt-in because its key bundle and private execution configuration are external fixtures. Set `NIGHTLEAN_TEST_BUNDLE`, `NIGHTLEAN_TEST_MANIFEST_SHA256` and `NIGHTLEAN_TEST_PRIVATE_CONFIG`, then run:

```sh
cargo test --manifest-path runtime/Cargo.toml --locked --test verified_assembly -- --ignored
```

This test accepted the qualified private claim bundle, rejected modified plan/key/profile payloads and a wrong digest before private configuration access or output creation, then removed the entire public source directory and successfully assembled from retained bytes. The normal default test suite does not substitute synthetic keys for this qualification. The raw C ABI remains a separately documented trusted-artifact boundary pending a higher-level verified-bundle binding.
