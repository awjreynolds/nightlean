# Feature-equivalent Nightlean

The active goal is verified feature equivalence with the pinned Compact capability baseline, expressed through Lean and native Midnight execution. The compiler and primary lowering remain Lean 4. Compact is reference material only and must not become a compiler, runtime, or mandatory test dependency.

## Baseline

The latest stable feature reference checked on 2026-11-16 is Compact toolchain 0.36.1, language 0.28.0, at source revision `7fa3a117c5e7efe9d2c51da04263e5f0b3509144`. The public-network matrix still lists 0.36.0. The newer source release bundles ZKIR 3.2.1; Nightlean's accepted local claim uses independently built ZKIR 3.2.0. These profiles must remain distinct until qualification establishes compatibility.

The [baseline report](../research/compact-equivalence-baseline.md) and [machine inventory](compact-feature-matrix.json) contain the source register, version distinctions, observed implementation gaps, and acceptance requirements. The initial 221 entries are inventory records, not independent delivery units or a percentage-complete score. All equivalence results are unverified.

## Required outcomes

- Equivalent contract capabilities and observable semantics across the baseline's types, expressions, bounded control flow, functions/modules/generics, private execution, disclosure, ledger ADTs, cryptography, contracts, events and assets.
- Native ZKIR, ledger artifacts, proof and transaction construction, with canonical encodings and reproducible provenance.
- A host-neutral runtime and provider ABI, usable without Node by a Rust application, with qualified C/C++, Kotlin, Swift, TypeScript and portable WASM options.
- Explicit private-state and transaction failure/commit rules, bounded execution and host-capability handling.
- Feature-specific positive, negative, malformed-input, adversarial, composition, cross-host, and ledger acceptance evidence.
- Correctness proofs for internal transformations, clearly scoped external conformance, and independent review before production use.

Unrestricted general-purpose Lean compilation and duplication of wallet UIs, indexer services or explorers are separate products. Missing language or native integration capabilities must remain visible in the matrix. An unavailable upstream API is a blocker to record, not a reason to declare equivalence.

## Execution tracks

1. Expand the source inventory into executable semantic cases and qualify the current toolchain profile, including the Boolean-deserialization and Jubjub key-generation patch regressions.
2. Replace the mandatory JavaScript execution path with a native Rust reference runtime using the existing source-generated private-claim vectors. Define a versioned provider protocol and canonical artifact ABI. See [portable runtime design](../designs/portable-runtime.md).
3. Add bounded integers, conversions, composite values and function/control-flow facilities to the typed Lean representation, elaborator, evaluator and native lowering.
4. Complete scalar state operations, constructors and sealed fields, then collections, nested ADTs, tree operations and Kernel effects with ledger-backed tests.
5. Add the complete cryptographic, contract-call, event and asset capability set, split into bounded implementation packages with feature IDs and native evidence.
6. Qualify native host bindings, optional WASM execution, mobile packaging, private-state lifecycle and provider capabilities against the same artifacts and conformance vectors.
7. Finish assurance, release documentation, developer packaging and the feature-equivalence evidence audit.

These tracks contain dependencies, not a delivery estimate. The public issue map is the source of truth for claim ownership, current blockers and implementation order.

## Present evidence

The [native private-claim POC](../development/native-localnet.md) demonstrates one source program through native ZKIR and finalized local ledger execution. It does not demonstrate feature parity, a Node-free application runtime, general witness callbacks, mobile SDKs, or complete formal verification. Those gaps are part of this active goal.
