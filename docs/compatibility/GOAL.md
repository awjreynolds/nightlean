# Full native-capability Nightlean

The active goal is full coverage of the pinned ZKIR v3 implementation and native Midnight ledger contract capabilities, with verified Compact feature equivalence as a minimum coverage check. The compiler and primary lowering remain Lean 4. Compact supplies engineering lessons, source-semantic evidence and regression ideas. It must not become a compiler, runtime, or mandatory consumer dependency, and its exposed features do not cap Nightlean's scope.

The user's 2026-11-16 clarification explicitly adds native composability beyond Compact's current exposure and compiler checks for guarded disclosure of private state into public state. Existing scalar, runtime and artifact work continues under this expanded destination.

Proof-backed functional correctness and contract auditability are core delivery requirements. Authors use ordinary Lean specifications, theorem syntax, tactics and proof libraries. Circuit execution follows a finite compilable subset, while theorem authoring uses Lean's full proof language. A verified-contract claim must identify its exact specification, checked theorems, preserved compilation path, deployed artifacts and remaining assumptions.

## Baseline

The latest stable feature reference checked on 2026-11-16 is Compact toolchain 0.36.1, language 0.28.0, at source revision `7fa3a117c5e7efe9d2c51da04263e5f0b3509144`. The public-network matrix still lists 0.36.0. The newer source release bundles ZKIR 3.2.1. Nightlean preserves its accepted 3.2.0 default and now provides a [selectable 3.2.1 compiler/runtime profile](../development/zkir-3.2.1-integrated.md). An isolated exact-commit build produced authenticated public bundles and finalized claim/scalar deployments and calls with matching state bytes. The earlier [experimental qualification](../development/zkir-3.2.1-qualification.md) remains separate historical evidence. These selected workflows do not qualify every capability or a public network.

The [baseline report](../research/compact-equivalence-baseline.md) and [machine inventory](compact-feature-matrix.json) contain the source register, version distinctions, observed implementation gaps, and acceptance requirements. The initial 221 entries are inventory records, not independent delivery units or a percentage-complete score. All equivalence results are unverified.

## Required outcomes

- Every type and instruction in the pinned ZKIR v3 implementation has an explicit source mapping, type/precondition rules and execution evidence, or a recorded upstream blocker. Deprecated operations receive explicit compatibility or tested replacement handling. Raw parser support is not source support or ledger acceptance.
- Equivalent contract capabilities and observable semantics across the baseline's types, expressions, bounded control flow, functions/modules/generics, private execution, disclosure, ledger ADTs, cryptography, contracts, events and assets.
- Native-ledger contract composability, including capabilities not yet exposed by Compact, qualified against actual call claims, entrypoints, keys, communication commitments, state effects and failure behavior.
- Compiler-enforced information-flow rules for both private value dependencies and private control dependencies at public outputs, ledger writes, events and contract calls. A constant public write under a private guard still requires explicit authorized disclosure. Track provider/private-state origins and classify assertion/failure side channels separately.
- Native ZKIR, ledger artifacts, proof and transaction construction, with canonical encodings and reproducible provenance.
- A host-neutral runtime and provider ABI, usable without Node by a Rust application, with qualified C/C++, Kotlin, Swift, TypeScript and portable WASM options.
- Explicit private-state and transaction failure/commit rules, bounded execution and host-capability handling.
- Feature-specific positive, negative, malformed-input, adversarial, composition, cross-host, and ledger acceptance evidence.
- Correctness proofs for internal transformations, clearly scoped external conformance, and independent review before production use.
- Contract-specific preconditions, postconditions and invariants, with proofs over the actual source definitions and explicit non-vacuity evidence. A disconnected helper lemma or a theorem of an unrelated proposition does not establish contract correctness.
- A mandatory proof/audit chain: kernel-checked proof terms, transitive axiom policy, exact theorem-statement/contract identity matching, proof/import/toolchain provenance, compiler/lowering preservation and binding to the emitted circuit, native plan, keys and deployed entrypoint.
- Audit-readable proof obligations and assumptions, including native semantics, cryptography, proving/verifying implementations and host/private-state behavior. Tests and accepted receipts supplement this chain. They do not replace missing preservation proofs or authorize an unqualified verified-contract label.
- A separate privacy specification and proof obligation for proof-qualified private contracts. Define the observer, public inputs/state/results/events/calls/transcript activity, authorized releases and validity/failure scope. Prove public observations do not reveal further private differences, then preserve that property through compilation. Functional correctness alone never implies confidentiality. Proof-byte privacy requires the proving system's stated zero-knowledge assumptions; host services, logs and timing need their own scope.

Unrestricted general-purpose Lean compilation and duplication of wallet UIs, indexer services or explorers are separate products. Missing language or native integration capabilities must remain visible in the matrix. An unavailable upstream API is a blocker to record, not a reason to declare equivalence.

## Execution tracks

1. Expand the source inventory into executable semantic cases and qualify the current toolchain profile, including the Boolean-deserialization and Jubjub key-generation patch regressions.
   Audit the complete native ZKIR type/instruction surface independently of the Compact inventory. Use source-derived preconditions and targeted proving/ledger tests to choose implementation packages.
2. Replace the mandatory JavaScript execution path with a native Rust reference runtime using the existing source-generated private-claim vectors. Define a versioned provider protocol and canonical artifact ABI. See [portable runtime design](../designs/portable-runtime.md).
3. Add bounded integers, conversions, composite values and function/control-flow facilities to the typed Lean representation, elaborator, evaluator and native lowering.
4. Complete scalar state operations, constructors and sealed fields, then collections, nested ADTs, tree operations and Kernel effects with ledger-backed tests.
5. Add the complete cryptographic, contract-call, event and asset capability set, split into bounded implementation packages with feature IDs and native evidence.
   Implement disclosure analysis over the typed source/IR before exposing guarded public effects. Learn from Compact's dependency and control-flow analysis, then justify and test any differences against Nightlean's native architecture.
6. Qualify native host bindings, optional WASM execution, mobile packaging, private-state lifecycle and provider capabilities against the same artifacts and conformance vectors.
7. Finish assurance, release documentation, developer packaging and the feature-equivalence evidence audit.
   Contract proof authoring, theorem registration, kernel replay/axiom auditing and native preservation are implementation tracks throughout development. They are mandatory gates for the verified product, rather than work postponed until feature breadth is complete.

These tracks contain dependencies, not a delivery estimate. The public issue map is the source of truth for claim ownership, current blockers and implementation order.

## Present evidence

The [native private-claim POC](../development/native-localnet.md) demonstrates one source program through native ZKIR and finalized local ledger execution. The [Rust runtime](../development/native-rust-runtime.md) reproduces its state and checker preimage without Node. The [C ABI](../development/native-runtime-abi.md) also executes the claim in linked C++ and validates resumable scalar-input requests. Scoped host providers and [private journals](../designs/private-state-lifecycle.md) now have a tested transaction-bound lifecycle with private-only transport and correlated compare-and-swap. Durable storage and truthful acceptance evidence remain host assumptions. General source witness functions, proof generation and submission through the ABI, mobile/WASM SDKs, full feature parity and complete formal verification remain outstanding.

The [scalar slice](../development/unsigned-localnet.md) implements source-backed unsigned bounds, conversions, canonical ABI values and native range constraints. Thirty-four raw-witness cases pass against both qualified checker releases. The Rust-assembled integer contract has finalized local deployment/call and exact state-byte evidence. Nominal aliases, additional scalar operators and full feature equivalence remain outstanding.

The mandatory [scalar disclosure pass](../development/disclosure.md) tracks private value and control origins at current public sinks. An authorized-release native proof binds every tested public field. This is scoped data-flow enforcement, not a theorem covering failure, timing, host logs or every future native primitive.

The [native producer gate](../development/native-producer-safety.md) validates every currently emitted scalar relation before artifact emission. Its registry names all 47 instructions and 15 native value types, enables 16 current instructions over Native fields and rejects unsupported entries. Sixty-five producer cases and targeted native observations cover current typing, range, SSA, assertion, output and public-binding rules. Formal source-to-native preservation remains separate.

The [composite type foundation](../development/composite-types.md) defines nominal/structural identity and checked layouts with proof-linked leaf, logical-expanded and retained-node bounds. Aggregate values, cross-host codecs, native aggregate proof fixtures and component disclosure integration remain dependent implementation work. The type/layout module alone does not expose aggregate source execution.

The [actual private-claim source proofs](../development/private-claim-proofs.md) establish source eligibility equations, invariant preservation, exact state updates, framing and replay rejection. A two-run theorem establishes equal successful source observations under the declared public-input policy. Six valid source mutations each break their expected proof clause. Hash semantics and canonical inputs remain explicit assumptions rather than cryptographic secrecy claims.

The [standalone native claim relation proofs](../development/private-claim-lowering-proofs.md) establish arbitrary-satisfying-witness soundness, source completeness and pruning composition under a named hash agreement. A kernel-checked JSON-tree certificate covers the actual emitted scalar relation, including public return binding through Impact. Altered path wiring and an omitted root assertion fail their certificates. Raw byte parsing, authenticated builds and full ledger state/transcript preservation remain open.

The [source proof-audit foundation](../development/proof-registration.md) provides typed functional/privacy obligations, model-digest authentication, fresh kernel replay, exact statement checks and transitive axiom policy. The actual private-claim policy now passes both source obligations, with wrong-policy and changed-source rejection evidence. Checked counterexamples separate functional correctness, successful-only privacy and failure-channel privacy. Native relation/state/transcript preservation, exact-artifact certificates and deployed key/operation binding remain mandatory open gates. No source proof or accepted receipt establishes the complete verified-contract chain alone.
