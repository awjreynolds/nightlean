# Disclosure policy

Noctium rejects undisclosed private value and control origins at the current public source sinks. The executable policy lives in `Noctium/Disclosure.lean`. The Lean compiler checks source declarations, checks again before artifact emission, and applies the policy at the public typed-IR ZKIR and Impact lowering entrypoints.

The scalar policy shares the public-sink checks with [component-aware helpers](component-disclosure.md) and [typed witnesses](typed-witnesses.md). The compiler tracks source value origins separately from accumulated control origins.

## Values and authorization

Private parameters carry their name and source span as private origins. Explicitly public parameters and authenticated public-ledger reads have public origins. Every current scalar operator has an explicit propagation rule:

- Arithmetic, comparisons and casts preserve operand origins.
- Poseidon hashes preserve operand origins. Hashing grants no automatic permission to publish a result.
- Eager `select` combines origins from its predicate and both operands, including a constant selection. This is conservative value-flow analysis of the existing eager operator, not structured branch analysis.
- Missing origin bindings reject. The typed expression match is exhaustive, so a new native/scalar expression constructor requires an explicit rule before the analysis builds.

Use `disclose(value)` to authorize a particular value at a visible source location. The annotation retains a `SourceSpan` in the typed AST. It neither publishes the value by itself nor changes its computation, range checks or proof constraints. The existing native JSON and ZKIR lowerers erase the annotation, preserving their ABI and witness layout.

```lean
noctium_circuit release where
  private secret : UInt 8
  output result : UInt 8 := disclose(secret)
end
```

`select(flag, disclose(1), 0)` still carries a private `flag` origin and rejects at a public output or write. `select(disclose(flag), 1, 0)` authorizes the predicate value used by that expression. Disclosing the whole selected result also authorizes that result. Another occurrence of the original private flag stays private.

The analysis keeps active control origins separate from payload origins through `checkSink` and the entrypoint control-context argument. Structured guards accumulate their predicate origins. Each public effect checks the inherited control alongside its own guard, including effects with no local condition.

## Public sinks and origin fixtures

All circuit outputs and entrypoint returns are public sinks. The exhaustive `Disclosure.describeEffect` registry classifies ledger effects by public transcript family, guard policy, selectors, payloads and result bindings. The checker validates public activity, paths and payloads before adding any read results to the public environment. Proof-only predicates keep their private origins.

Assertions and `require` represent the intended proof relation. Their private predicates receive propagation analysis but do not act as ordinary public value-flow sinks. Proof success, failed assertions, invalid casts, rejected transactions, callback failures and execution timing require a separate information-release model.

Provider and private-state origins label declared inputs through `Circuit.privateOrigins`. The checker rejects duplicate labels, undeclared names, duplicate input names and privately labeled public inputs. The [typed private state route](typed-witnesses.md#private-state) retains the private read and stage boundaries. Arbitrary private-state effects inside reusable helper bodies remain gated by the helper compiler.

Source entrypoint operands include private circuit parameters so an explicit release is expressible. Type checking alone grants no permission to disclose them. The mandatory disclosure gates decide whether a public use is authorized. `Entrypoint.run` also applies the policy before its reference ledger transition.

Source-generated entrypoints retain one source span per effect. Nonempty `effectSpans` metadata must match the effect count exactly. Older hand-built typed IR with no per-effect metadata uses its entrypoint span. Diagnostics identify the originating private value, origin location, public sink and sink location.

## Pinned native descriptors

The [machine inventory](../compatibility/zkir-feature-matrix.json) records the ZKIR 3.2.1 opcode and value-type privacy rules and the Ledger 9 Impact VM roles. The producer reads operation descriptors to match input visibility, public read guards, Impact bindings and returns to the independently derived source statement. Value-type rows cover qualified representations. In particular, typed Bool, Byte and Bytes intermediates have narrower routes than the public source ABI.

Enabled rows have a descriptor for their scoped route. Gated rows omit source emission, including the seven deprecated opcodes. An unavailable capability requires an absent pinned implementation. Raw Impact instructions remain internal to compiler-generated transcripts. Their results, selectors, payloads and activity bind to the checked source plan.

Call descriptors check the public address, entrypoint hash, communication commitment and activity. The selected scalar composition commits private argument and return data in the native communication binding. The published commitment requires explicit authorization. [Native call claims](native-call-claims.md)

Event descriptors check payload and activity independently. The [guarded event fixture](../../tests/disclosure/authorized-event-guard.lean) explicitly releases both. The native checker validates both activity branches and rejects a changed public transcript. The CLI fixture independently removes each release and verifies rejection before creating the artifact directory.

## Failure and observer scope

The public-sink policy covers returned values and the payload, selection and activity of public effects on successful execution. A failed assertion or rejected proof exposes a success or failure outcome to anyone allowed to observe that attempt. A finalized transaction exposes its public acceptance and failure classification. These outcomes belong to the observer's model alongside the explicitly released data.

Compile diagnostics report static source names and spans. The native host, proof and client interfaces return bounded error categories and public receipt information. Provider arguments, replies, private keys and staged writes use the private host channels. Host logging, callback side effects, timing, termination and resource usage remain outside this guarantee. [Native proof errors](native-proof-api.md) · [Native client recovery](native-client.md#host-boundaries-and-recovery) · [Private claim observer](private-claim-native-privacy-proofs.md#exact-policy-and-observer)

## Checked invariants

Lean checks these policy and transformation statements:

- `Disclosure.sink_accepts_iff`: a sink accepts exactly when both its payload and active control origin lists are empty.
- `Disclosure.payload_release_preserves_control_rejection`: an empty payload origin list does not authorize a private control context.
- `Disclosure.disclosed_value_origins`: an analyzed disclosure clears only the wrapped expression's returned origins.
- `disclose_evaluation`: disclosure does not change scalar evaluation, including errors.
- `Passes.pruneCircuit_disclosure` and `Passes.pruneEntrypoint_disclosure`: literal-true pruning preserves the complete disclosure-check result for any control context.

The existing validation and executable-semantics pruning theorems still hold. These are scoped proofs about the implemented policy and transformations. They do not prove the entire compiler, native backend or cryptography correct.

## Reproduce the source and typed-IR checks

```sh
lake build
lake env lean tests/Disclosure.lean
lake env lean tests/BoundedScalars.lean
bash tests/disclosure-cli.sh
bash tests/uint-cli.sh
```

The disclosure CLI cases reject direct private data, hashes, private selection predicates, payload-only permission, unrelated later uses, private map paths and private-dependent effects before creating an artifact directory. They also compile explicitly authorized examples. The unit cases exercise provider and private-state labels, inherited control, metadata validation and direct backend entrypoints.

Run the guarded event's native checker with fresh 3.2.1 artifacts.

```sh
out="$PWD/build/experiments/private-event-guard"
.lake/build/bin/noctium compile tests/disclosure/authorized-event-guard.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --emit ledger --output "$out"
NOCTIUM_EVENT_ARTIFACTS="$out" cargo test --manifest-path runtime/Cargo.toml \
  --locked --no-default-features --features zkir-321 --test standard_events \
  standard_events_bind_payload_order_and_activity -- --ignored
```

Intentional releases in the scalar conformance sources now use explicit annotations. All 17 generated scalar artifact files match the pre-policy files byte for byte. The existing private-claim source already returns public input values and keeps its accepted native circuit hash unchanged. The explicit release example in `examples/Disclosure.lean` supplies the native checker/prover qualification fixture.

## Compiler-bypass boundary

The compiled runtime plan contains the authorized program, not a record of source taint history. Annotation erasure leaves the native ABI unchanged. The Rust runtime validates the plan's supported schema and value ranges, but does not infer whether a handwritten plan had authorized source disclosure.

Handwritten ZKIR, raw runtime plans and the lower-level `Expr.eval`, `Circuit.run` and `runEffects` reference primitives therefore have a separate trust boundary. They do not replace the compiler policy gate. Consumers must authenticate compiler-produced bundles and their declared provenance. Manifest hashes identify bytes. They do not prove compiler correctness or authorize an otherwise unreviewed program.

## Native qualification

[Machine evidence](../../tests/disclosure/native-evidence.json) records the actual authorized source, native keys, public parameter hash and proof digest. Eight raw-witness cases pass against both official 3.2.0 and 3.2.1 checkers, bypassing runtime validation. Wrong public values, a changed released result, out-of-range values and a malformed Boolean reject.

Independent native key generation produced k5 keys for `authorizedRelease` at 13 rows. The loopback native proof server generated and self-verified a 3,468-byte proof. A separate Rust verifier accepted this proof with its real verifier key and the source-pinned k5 parameters. Changing the binding input, public parameter, released output or proof bytes made native verification fail. These are cryptographic verifier checks, separate from preprocessing rejection. No ledger transaction was submitted for this fixture.

After reproducing the source, keys, proof and pinned parameter file in one directory, run the explicit native verification test:

```sh
NOCTIUM_DISCLOSURE_FIXTURE=/path/to/qualification \
  cargo test --manifest-path runtime/Cargo.toml --locked \
  --test disclosure_verification -- --ignored
```

The directory must contain `authorizedRelease.verifier`, `authorizedRelease.proof` and `bls_midnight_2p5`. The test checks the parameter file against its pinned SHA-256 before verification. This qualifies the authorized emitted relation. The separate compiler policy decides whether a source release is authorized, and complete source-to-native preservation remains a mandatory open proof obligation.
