# Native proof construction and verification

The Rust library builds and proves the current source private claim in process. Applications do not need Node, Compact, a shell command or a toolkit subprocess for this proof stage. `noctium_runtime::proof` uses the selected pinned native ZKIR implementation and the official ledger's typed proof attachment path.

This Rust API covers one frozen contract call with no offers or dust actions. Source-bound skipped transcript groups use native Noop attachment and gas accounting. The selected-3.2.1 conditional-write case has real proof and attachment evidence. The published C ABI provides a separate phase A native proof interface; it also stops before funding, signing, submission, receipt validation or journal persistence. Mobile/WASM SDKs remain unqualified. A locally verified proof establishes the retained verifier key's relation for the exact native statement. This is not a general theorem connecting Lean source, compiler output and generated keys. `compiled_verified` stays false. See [native proof ABI phase A](native-proof-abi.md) for the C ABI guide and qualification evidence.

## Application sequence

1. Authenticate the bundle with `artifacts::verify(path, Some(trusted_manifest_sha256))`. The digest comes from an external trusted channel. Integrity-only `verify(path, None)` remains available to existing low-level tools, but the proof API rejects such a bundle before parsing private input.
2. Supply trusted parameter bytes and their independently trusted SHA-256 digest to `TrustedParameters::from_bytes(bytes, k, digest)`. The loader checks the digest, the actual little-endian degree header and the exact bounded length before native allocation. It uses checked native raw decoding for every G1/G2 point, including canonical encoding, curve and subgroup checks. A matching digest authenticates the supplied bytes. Ceremony provenance and the required algebraic relations between SRS points remain external trust assumptions. The host owns parameter distribution and storage.
3. Build `PreparedProof::from_config(&bundle, private_config, ttl, &mut host_rng)`. The constructor uses retained circuit, keys, plan and ledger parameters, validates public material first, then parses private input. The host supplies cryptographic entropy and an explicit TTL. The core opens no files or sockets. `deployment_intent()` exposes the matching native deployment intent if the host needs a new contract.
4. Call `prepared.prove(&service, &parameters, response_limit, stop_future).await`. `LocalProver::new(host_rng)` proves inside Rust. Another `ProofService` implementation performs explicitly authorized local-worker or remote work. The core verifies the returned proof locally before the ledger attaches a typed proof.
5. Consume `ProvedIntent::native()` or `serialized()`. These become available only after proof verification, attachment, statement comparison and exact native serialization roundtrip. They do not represent a funded or submitted transaction.

`PreparedProof::verify_response` verifies a previously obtained proof-service response against the frozen call without attaching or submitting anything. `PreparedProof::from_intent` freezes a host-constructed native preimage intent against the authenticated bundle. This first version accepts a single call and rejects offers and dust. `private_intent_bytes()` explicitly exports witness-bearing retry material and requires private storage.

The library retains the authenticated bundle bytes. Proof services do not resolve keys from mutable paths. `ProofService` returns a fixed `ServiceError`, so HTTP bodies, witness values and native parser causes do not enter diagnostics. API errors contain fixed codes and discard nested value-bearing causes.

Authentication does not imply valid native key encoding. Before native key initialization, the loader checks bounded outer and inner degrees against the retained circuit, verifier architecture against the circuit's selected chips, exact commitment counts and byte lengths, and fixed/permutation polynomial dimensions. The proving key must embed the exact canonical retained IR relation. Checked native raw decoding validates proving-key points and scalars. The initialized typed proving key stays retained for local proving, avoiding the upstream unchecked key reader. Raw key payloads are capped at 128 MiB. These checks reject malformed authenticated public material before private configuration parsing. Trusted key generation and the cryptographic correspondence between retained keys and circuit remain external assumptions.

## Multi-entrypoint POC

The multi-entrypoint POC uses `ContractBundleSet` and
`WitnessContractTarget::from_state_config` to retain a complete operation map
and one deployment address. `target.start_deployment_client` starts that
deployment through the native client. After finalized receipt validation and
private journal commit, `WitnessClient::current_state_context` issues an opaque
one-use state token. `target.operation` selects an operation with its own trusted
parameters and fresh call TTL. `WitnessExecution::begin_contract_operation`
borrows the operation target and a mutable `Option<CurrentStateContext>`, checks
those identities before source callbacks, then
`prepare_contract_proof` retains the same invocation runtime for proof and client
handoff. Later calls use current state at the original address.

This path has a selected-3.2.1/localnet-feature build and a focused
operation/successor binding test. It has not yet completed the multi-operation
localnet demonstration in issue 67. Recovery-loaded clients do not restore state
tokens and fail closed. The token identifies a validated checkpoint, without a
new latest-state RPC check. The single conditional-write proof case below does
not establish a complete multi-operation lifecycle.
Rejected construction leaves the token in the caller's `Option`. Successful
construction takes it. Before proof preparation,
`cancel_contract_operation` clears and drops the source session and returns the
same token for a corrected retry. Generic `cancel` rejects this mode to prevent
accidental token loss. Proof preparation consumes the token, so later
cancellation cannot return a second owner. Process recovery and post-preparation
restoration remain separate work in issue 67.

One focused selected-3.2.1 lifecycle test covers rejected input, cancellation
after source failure, corrected retry and token consumption at preparation. It
uses the retained scalar witness bundle without a new proof or deployment.

Contracts without a witness-control sidecar use
`operation.prepare_call(&mut current_state, &parameters, scalar_inputs, &mut rng)`.
This validates the selected operation's parameter identity and admitted state
before construction. Errors preserve the token. Success consumes the token and
returns the same `PreparedProof` used by the native prover.
After proving, `target.start_call_client(&operation, &mut proved, descriptor, setup)`
checks the retained deployment, operation and state binding before starting the
client with explicit host setup. Failed startup preserves the proved value.
No synthetic witness plan or Node process is required.

The focused PublicSupply test uses authenticated add/subtract bundles with k9/k8
parameters. It checks state transitions 0→5→3, parameter and foreign-state
rejection, and client startup after one real addSupply proof. Its state-token
admission is test-only. It does not establish finalized ledger execution or
complete issue 67's multi-operation localnet lifecycle.

## Native phase and statement

The pinned ledger's `Intent::prove` checks circuit activity, rewrites skipped transcript groups, derives binding from the resulting call and the parent intent commitment, then requests a proof with the exact binding override. Noctium previews its Noop insertion/merging and added compute gas before freezing the expected statement. Checked arithmetic rejects invalid counts and overflow. The preview calls native `ContractCall::public_inputs(parent_binding_commitment)` for the binding calculation. Actual attachment still uses `Intent::prove`, and the adapter requires its binding override and final statement to match the frozen preview.

One focused selected-3.2.1 test proves the inactive conditional-write source
fixture. Its attached transcripts and gas match the preview, including 26 skipped
fields. Changing one skipped zero statement field to 1 rejects the proof while
all other statement fields stay fixed. This is proof/attachment evidence without
a ledger deployment or a broader guarded-language claim.

The same test proves the private-only `Issue43EmptyActivity` fixture with zero
active VM operations. Assembly retains an empty guaranteed transcript from the
native empty-query result, including its gas, effects, version and state. This
gives the official attachment path a segment for its Noops without introducing
a dummy source input or operation. The two fixtures use their own k7 and k6 keys
and trusted parameters.

The opt-in test is
`proof::tests::inactive_guarded_write_matches_native_noop_preview_and_binds_skipped_fields`.
Supply `NOCTIUM_ISSUE43_BUNDLE`, `NOCTIUM_ISSUE43_MANIFEST_SHA256`,
`NOCTIUM_ISSUE43_PRIVATE_CONFIG`, `NOCTIUM_ISSUE43_PROOF_PARAMETERS`, and
`NOCTIUM_ISSUE43_PROOF_PARAMETERS_SHA256`, then run:

```sh
cargo +1.100.0 test --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321,localnet \
  --lib proof::tests::inactive_guarded_write_matches_native_noop_preview_and_binds_skipped_fields \
  -- --ignored --exact
```

Use the compiled `Issue43ConditionalWrites` fixture and matching independent
native keys. Also supply the five corresponding `NOCTIUM_ISSUE43_EMPTY_*`
variables for the compiled `Issue43EmptyActivity` fixture. Keep invocation
configurations outside their public bundles.

The expected statement includes the native binding input, communication commitment and both transcript parts' field representations. The wrapper verifies the actual returned proof with the retained verifier key and trusted verifier parameters against this exact vector. It repeats verification after typed attachment and rejects any changed statement or serialization.

The frozen intent is the proving boundary. Changes to the contract, entry point, bound effects/gas/transcript, communication commitment or parent intent commitment require a new prepared context and proof. Later funding and balancing must preserve these fields or re-prove. The current API does not claim to finish those later transaction stages.

## Service and response contract

`ProofService::prove` receives a `ProofRequest` with no `Debug` implementation. The request includes retained proving material, the exact private preimage and trusted parameter identity. The host chooses and authorizes the service. Remote proving discloses witness material to that service and needs an explicit application privacy decision.

`ProofRequest::private_wire_payload()` returns a best-effort zeroizing private buffer using the pinned proof server's native tuple encoding:

```text
(ProofPreimageVersioned::V2(preimage_with_exact_binding),
 Some(retained_proving_key_verifier_key_and_IR),
 None::<Fr>)
```

A host network adapter sends those bytes itself, applies its own endpoint policy and caps response allocation while reading. The core does not create an HTTP client or invoke a child process. Both local and remote adapters return the native tagged `ProofVersioned::V2(raw_proof)` response envelope used by the pinned `/prove` endpoint. This transport envelope is distinct from the final ledger call's `ProofVersioned::V3`, selected upstream for the retained `verifier-key[v7]`. Unsupported response versions, trailing bytes, truncated encodings and oversized responses fail before attachment.

`ProofRequest::prove_locally(host_rng)` runs the selected native prover with the supplied trusted parameters. It compares the native prover's returned statement to the exact frozen native statement. `LocalProver` owns one host-supplied RNG and is one-use. A retry creates a fresh adapter with fresh entropy. Native construction and local proving use separate entropy sources supplied by the host.

Intent construction samples the nonzero communication field using at most 128 canonical 32-byte attempts. Zero-only and noncanonical-only host RNGs return a fixed private-input error. This bound prevents rejection loops in construction. The host still supplies a functioning cryptographic RNG, including for native proof generation.

The response cap is explicit and bounded by 1 MiB. Parameter bytes are capped at 128 MiB. Core response checks run after a custom provider returns its buffer. A provider must enforce the request cap before allocating or receiving an unbounded response. Private wire/request material has no ordinary result JSON or diagnostic representation. Native preimages zeroize on final drop, exported wire payloads use `Zeroizing`, and callers own any private bytes exported for storage. Upstream cryptographic code and copies impose best-effort zeroization limits. Applications should avoid enabling upstream trace logging around private execution.

## Cancellation and timeout

The application supplies a future yielding `Abort::Cancelled` or `Abort::Deadline`. The core polls this future before proof work and races it against the service future without requiring Tokio or a timer thread. An already-fired stop prevents the service from receiving private material. A stop during a pending service drops the service future and returns a fixed error. No attached intent escapes failure, cancellation or timeout.

Dropping a network future does not guarantee cancellation of work already accepted by a remote service. CPU-only native proving performs blocking work during a poll and does not support hard preemption from an asynchronous stop. A host needing hard CPU deadlines uses an isolated worker with an explicit termination policy. The core does not spawn or terminate such a worker. Retries preserve the exact frozen statement and require fresh proving entropy. Neither retry nor cancellation commits private application state or submits transactions.

## Reproduce native qualification

Build the selected profile explicitly. The default remains 3.2.0. The integrated 3.2.1 build uses:

```sh
cargo test --manifest-path runtime/Cargo.toml --no-default-features --features zkir-321 \
  --test native_proof -- --include-ignored
```

The opt-in test reads `NOCTIUM_TEST_BUNDLE`, `NOCTIUM_TEST_MANIFEST_SHA256`, `NOCTIUM_TEST_PRIVATE_CONFIG`, `NOCTIUM_TEST_PROOF_PARAMETERS` and `NOCTIUM_TEST_PROOF_PARAMETERS_SHA256` from the test host. It generates a real proof in Rust, verifies and attaches it through the native ledger, checks serialization, and rejects invalid response versions, malformed/trailing/truncated/oversized bytes, corrupt proofs, changed contract and intent binding, and inconsistent communication commitments. It also tests cancellation before private disclosure and while a request is pending.

The ignored library test `proof::tests::real_crypto_rejects_each_statement_field_and_wrong_key` additionally takes `NOCTIUM_TEST_OTHER_VERIFIER`. It independently changes every public statement field and uses another real native verifier key. All mutations fail actual cryptographic verification. There is no mock-verification feature in this path.

Primary implementation sources are the pinned ledger `ledger/src/prove.rs`, `ledger/src/verify.rs`, `transient-crypto/src/proofs.rs`, `proof-server/src/endpoints.rs`, and the selected ZKIR `zkir/src/ir.rs`. Profile pins and previous ledger qualification are recorded in [native runtime profiles](zkir-3.2.1-integrated.md).
