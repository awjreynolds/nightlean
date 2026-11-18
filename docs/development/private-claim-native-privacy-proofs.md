# PrivateClaim native observation privacy

The actual PrivateClaim has a separate kernel-checked native privacy obligation. Two successful valid executions from the same canonical public state and context, with equal declared root, campaign and supplied nullifier, produce equal supported public observations. Their private inputs, internal SSA assignments and checked native VM traces need not match.

This is a scoped two-run property. It does not prove secrecy of the declared public nullifier, hash preimage secrecy, cryptographic proof-byte zero knowledge, host/provider confidentiality, failure privacy or timing privacy. Issue 58's formal model and JSON-tree composition are implemented. Full exact-artifact integration remains pending issue 56. Key/deployment identity remains issue 57. `compiledContractVerified` stays false.

## Exact policy and observer

`proofs/PrivateClaimNativePrivacy.lean` defines a typed native policy whose source field is exactly `Noctium.PrivateClaimVerification.policy`. The native observer identity is `successfulClaimPublicTranscriptV1`, its scope is `successfulOnly`, and the actual claim has no additional authorized private release. `NativePrivacyObligation policy` includes exact policy equality in its type. A changed scope, release policy or functional theorem cannot substitute for the required privacy theorem.

The public observer includes:

- Declared root, campaign and supplied nullifier, plus the returned nullifier.
- The complete modeled public state before and after execution.
- Six aligned Popeq read cells and their public scalar read stream.
- All 21 ordered native operations, complete opcode groups, index slots, saved paths, membership keys and insertion keys.
- The all-active mask and the empty contract input/output communication commitment.
- The final proof-phase binding public input under explicit `BindingAgrees` implementation agreement.

The returned-nullifier component records the source public result established by preservation and already present in the supplied public input. The native contract-call input/output interface stays empty. No additional native return channel is claimed.

`NativePrivacy.queries` projects existing index, member and insert operations. It introduces no source event, external call, structured guard or private-state host feature. Complete opcode payloads remain observable alongside the query projection.

Excluded observables are rejected outcomes, termination, timing/resources, proof bytes, host/provider access and host logs. The existing DF-00 failure fixture proves successful-only privacy and disproves all-outcomes privacy for the same supported source program. `wrong_scope_rejected` and the audit's wrong-scope cases prevent reusing this package as an all-outcomes theorem.

## Proof composition

`source_privacy_from_native` starts with arbitrary native scalar assignments satisfying the actual 55-instruction call and arbitrary checked VM traces over the actual 21-operation plan. It invokes issue 55's preservation theorem, which composes issue 54's scalar/hash relation with native state execution. Source success is derived, never supplied as a privacy premise. The proof then invokes the exact registered source privacy theorem from issue 53.

`operations_public` derives each observed opcode payload from native constraints. `native_observer_equal` combines source privacy with exact native successor/read preservation and proves equality of public values, native state, ordered operations, query paths, aligned/scalar reads, opcode groups, activity and communication commitment. Arbitrary private witness data are absent from the resulting observation equations.

`bound_native_privacy` also compares the actual proof-phase binding scalars supplied by the native statement. Each scalar must satisfy `BindingAgrees` with the public binding view. This is a named primitive/implementation premise, not a proved statement about Rust serialization or a deployed verifier. `NativePrivacyObligation` requires this bound theorem. Its binding view contains only observed public call fields and the shared public parent context.

`decoded_bound_privacy` specializes the result to independently decoded plan/call JSON trees through exact checked decoder certificates. `decoded_obligation` packages that statement for certificate and release composition.

The model keeps native hash/VM/proof-system implementation assumptions separate from privacy. It reuses the explicit `HashAgreement` and state-model assumptions from issues 54 and 55. No collision resistance or injectivity assumption is needed for public-observation equality. `NativePrivacy.ProofByteZeroKnowledge` is a named optional assumption interface for a future observer containing proof bytes. No inhabitant or zero-knowledge theorem is supplied here.

## Coupled host context and binding

Both runs receive the same `HostContext`: public parent context and communication randomness. The parent-context vector must encode every public transaction/context input consumed by the real binding implementation, including any address, entrypoint, partition, fee/parameter and public nonce data. The vector encoding and its implementation correspondence are explicit obligations, not a verified serializer. Thus the commitment is equal for the same empty input/output contract interface. Choosing different randomness changes a public observation. The theorem does not authorize a host to encode a private witness in its selected coins, binding value or parent context. Applying the model to an implementation requires a witness-independent host policy and an appropriate coupling of its random choices.

The real proof binding must be computed from the shared public context and public call view. `BindingAgrees` states the precise external agreement required of that proof-phase binding. Equality follows from equal binding views. This proves neither binding-hash injectivity nor final deployed-statement identity.

Constructor preimages contain a zero binding placeholder. The proof phase later overrides that placeholder with the real bound statement. A constructor checker sample cannot establish this final binding path. The native sample records the distinction explicitly. Final proof-phase checks belong to the native proof API qualification and the remaining exact-artifact/deployment links.

## Progress and distinct private witnesses

`native_progress` reuses issue 55's source eligibility/completeness theorem under explicit 21-operation and map-entry admission bounds. Privacy does not assume every invocation succeeds.

`symmetric_path_flip` and `symmetric_eligible_native_pair` supply a hash-independent family of different valid private witnesses. Set the first sibling equal to the leaf. Flipping direction0 preserves both ordered child values, so the first node, root and nullifier remain unchanged for any agreed hash, including native Poseidon. The pair admits two native executions with equal observations. No hash collision assumption or constant-zero oracle is needed. These are alternative executions from the same initial state. Running the second claim after recording the first nullifier still fails replay protection.

The earlier two-private-input constant-zero fixture is retained as explicitly abstract nonvacuity evidence. It is not used to qualify native Poseidon.

## Authorized release and negative fixtures

`proofs/PrivateClaimPrivacyFixtures.lean` reuses the clean DF-00 source fixtures from `tests/Verification.lean`. Its positive `authorized_release_privacy` supplies the exact declared release function for the explicitly disclosed Boolean. The same program has a checked counterexample to no-release privacy. Functional correctness alone therefore supplies no confidentiality result.

Finite negative fixtures reject a direct private output, a private hash public output, a private membership query key and a constant public write under the current private-control-origin interface. Additional kernel equations show differing direct payloads, query keys and activity masks are observable. The control fixture does not claim unsupported structured source guards have been implemented. The hash fixture also exhibits equal authorized hash outputs with distinct preimages in an explicit abstract oracle, which rules out treating declassification as preimage secrecy.

The imported DF-00 test module contains intentionally untrusted axiom/admission/native-computation regression declarations. Required fixture roots depend only on the clean selected theorems. The exported privacy closure is audited and replayed, so none of those unrelated declarations enters an accepted proof dependency.

## Fresh audit and artifact boundary

Run:

```sh
python3 scripts/proofs/check-private-claim-privacy.py
```

Add the pinned native checker sample:

```sh
python3 scripts/proofs/check-private-claim-privacy.py \
  --native-checker /path/to/official-3.2.1/midnight_zkir_wasm_fs.js
```

The runner builds the actual source and proofs in a fresh temporary import directory, emits the actual plan/call through the selected target, quotes candidate JSON trees and kernel-checks their decodings. Direct private output, private hash payload, private activity guard and private query-key artifact mutations must fail their actual decoder equality certificates. Wrong scope, wrong release and functional-only substitutions also reject.

The audit exports and replays the required theorem/certificate closure and checks actual axiom declarations plus safety flags. Only `propext`, `Classical.choice` and `Quot.sound` are allowed. It also checks source functional, source privacy and the separate exact native privacy proof types against a retained model export. A privacy theorem over a weakened query observer and a stale proof against changed actual source both reject through declaration comparison before acceptance.

An independent trusted model export and digest are supported through `--trusted-model-export` and `--trusted-model-sha256`. Without those arguments, the runner uses a retained local regression baseline. A local baseline is not independent review of the business specification. The export checker reads data, compares declarations and replays terms. It imports no candidate modules or initializers.

`NativePrivacy.ExactArtifactBinding` exposes the remaining byte/build obligations: the actual parser must map retained bytes to the certified trees, and the authenticated build predicate must bind those bytes to the reviewed source identity. `exact_artifact_composition` joins those future arguments to the decoded bound-privacy obligation. No byte/build certificate inhabitant is supplied by this original foundation package. The parser and build predicate must themselves be pinned and qualified by issue 56. This interface does not authenticate UTF-8 bytes, import provenance, a compiler executable or keys.

Retained development evidence lives under `.noctium/audits/private-claim-privacy/`. The portable summary is `tests/private-claim-privacy-evidence.json`. The summary reports the policy, observer, exclusions, host/binding premises, required assumptions, rejected mutations and pending issue 56/57 links.

## Native sample scope

`tests/private-claim-privacy-checker.mjs` uses real native Poseidon with secret 42, campaign 9, sibling0 equal to the derived leaf, sibling1 23 and direction pairs (0,1)/(1,1). It uses the actual emitted plan/call, native partitioning and `Intent.addCall`, matching the Rust assembly path. Both actual constructor preimages pass the official 3.2.1 checker under shared nonzero communication randomness. The sample compares public fields, all opcode payloads, read values, paths, state and active-group metadata.

The sample also requires the deprecated JS `ContractCallPrototype.intoCall` path to reject for the same nonzero randomness. In the pinned legacy ledger-v9 JS adapter, that method supplies the randomness as commitment and ignores its parent-binding argument. `Intent.addCall` computes the proper commitment. This regression prevents silently falling back to a zero-randomness diagnostic or the deprecated constructor.

The adapter's constructor binding remains the zero placeholder. The sample labels final proof-phase override as unverified. It proves no zero-knowledge property of generated proof bytes and sends no transaction.

## Exact-byte integration

The later [exact artifact certificate](private-claim-artifact-certificates.md) instantiates this foundation interface for immutable public compiler commit `925164d0e17d994038d77d3b2b71c410619557d3`. Independent authority and candidate builds matched, and a separate kernel checker matched retained bytes to the concrete functional, completeness and privacy certificate. The [new receipt](../../tests/private-claim-artifacts-evidence.json) records the qualified source/tool/model identities and parent verification.

The original privacy evidence above retains its historical foundation-snapshot flags. The new certificate closes its byte/build integration obligation for the actual claim. The separate [deployment audit](private-claim-deployment-audit.md) now qualifies key generation and the selected deployed operation under explicit native and trusted-node assumptions. The observer, successful-run scope and excluded observables stay as stated above.
