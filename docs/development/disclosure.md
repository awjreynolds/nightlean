# Scalar disclosure policy

Noctium rejects undisclosed private value and control origins at the current public source sinks. The executable policy lives in `Noctium/Disclosure.lean`. The Lean compiler checks source declarations, checks again before artifact emission, and applies the policy at the public typed-IR ZKIR and Impact lowering entrypoints.

This is DF-00, the current scalar-language policy. Composite values, source functions, structured guarded effects, general providers and native-wide propagation require their own rules. Structured `if` statements remain unsupported. This pass does not establish timing, failure-channel or whole-program noninterference.

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

The analysis keeps active control origins separate from payload origins through `checkSink` and the entrypoint control-context argument. A disclosed payload never clears the surrounding control context. Future structured guards must accumulate and pass their predicate origins. No current source syntax creates structured guarded effects.

## Public sinks and origin fixtures

All circuit outputs are public sinks. Entrypoint checks cover public cell writes, map keys and values, membership/absence queries, map read paths, and the control context of public reads. A public ledger read binds a public result only after its path and control checks pass. Current native lowering still rejects unsupported map value reads.

Assertions and `require` represent the intended proof relation. Their private predicates receive propagation analysis but do not act as ordinary public value-flow sinks. Proof success, failed assertions, invalid casts, rejected transactions, callback failures and execution timing require a separate information-release model.

DF-00 provider and private-state fixtures label declared inputs through `Circuit.privateOrigins`. These labels only strengthen privacy. They never clear private visibility. Duplicate labels, undeclared names, duplicate input names, or privately labeled public inputs reject. The labels model scalar provenance for tests. They do not implement provider persistence or private-state lifecycle operations.

Source entrypoint operands include private circuit parameters so an explicit release is expressible. Type checking alone grants no permission to disclose them. The mandatory disclosure gates decide whether a public use is authorized. `Entrypoint.run` also applies the policy before its reference ledger transition.

Source-generated entrypoints retain one source span per effect. Nonempty `effectSpans` metadata must match the effect count exactly. Older hand-built typed IR with no per-effect metadata uses its entrypoint span. Diagnostics identify the originating private value, origin location, public sink and sink location.

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

The disclosure CLI cases reject direct private data, hashes, private selection predicates, payload-only permission, unrelated later uses, private map paths and private-dependent writes before creating an artifact directory. They also reject unsupported structured guards and compile explicitly authorized examples. The unit cases exercise provider/private-state labels, active control fixtures, metadata validation and direct backend entrypoints.

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
