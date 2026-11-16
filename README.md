# Nightlean

Nightlean is a Lean 4 compiler project for Midnight contracts. Its source elaboration, typed intermediate representation, reference semantics, and ZKIR relation lowering are implemented in Lean.

The active goal is [full native ZKIR v3 and ledger capability coverage](docs/compatibility/GOAL.md), with verified Compact feature equivalence as a minimum comparison. Compact supplies compiler engineering lessons and semantic reference cases. Its exposed features do not cap Nightlean's scope.

Proof-backed functional correctness and auditability are core requirements. Authors should state contract specifications and prove their properties using ordinary Lean theorems, tactics and libraries. The verified product must connect those proofs to the compiled native artifacts and expose its remaining assumptions. Current scoped Lean proofs and localnet receipts do not yet establish that complete chain.

The current source supports Native, Bool and bounded UInt scalars with a small expression/state effect set. Native Rust execution, linked C/C++ providers, public bundle verification and private intent assembly are implemented for this slice. A mandatory [scalar disclosure pass](docs/development/disclosure.md) checks current public sinks. Scoped host providers and [private-state journals](docs/designs/private-state-lifecycle.md) have a tested native lifecycle. General source witness functions, guarded execution, broader types and native composition remain open. The [native inventory](docs/compatibility/zkir-feature-matrix.json) records 47 instructions and 15 value types, with no full-family qualification claims.

The [actual private-claim source proofs](docs/development/private-claim-proofs.md) establish eligibility equations, state invariants, framing and replay rejection under explicit hash assumptions. A separate theorem covers equal public observations of successful runs. Six source mutations invalidate their expected semantic clauses. The [proof-audit foundation](docs/development/proof-registration.md) matches typed obligations to a pinned model, replays exported proofs in a fresh Lean kernel and rejects forbidden axioms. These are source guarantees. Native lowering preservation, exact artifact certificates and deployed verifier binding remain mandatory open gates.

The compilation path is Lean source → typed circuit and contract IR → ZKIR v3 and native Impact runtime plans → Midnight proving and ledger libraries. The compiler emits standalone circuit relations, native entrypoint relations, and typed runtime metadata. The selected POC target is an isolated ledger 9 localnet.

The actual private-claim source completed native deployment at finalized block 398 and a valid claim at block 401. Wrong secret, path, direction, root, and nullifier are rejected. Replay leaves state unchanged. [Native receipts and provenance](docs/development/native-localnet.md) record the tested source, independent ZKIR toolchain, keys, and transactions.

The [bounded integer example](docs/development/unsigned-localnet.md) also finalized deployment at block 1304 and a call at 1308. Rust assembled its real intents, and the accepted state exactly matches its prediction. Thirty-four raw-witness scalar cases pass against the official 3.2.0 and 3.2.1 checkers. These selected programs do not establish full feature equivalence.

The [selectable 3.2.1 profile](docs/development/zkir-3.2.1-integrated.md) now threads exact source identities through compilation, native runtime builds and authenticated retained bundles. An isolated compiler commit produced new finalized claim and scalar runs. The default 3.2.0 artifacts remain compatible. A mandatory [native producer gate](docs/development/native-producer-safety.md) checks current scalar invariants and rejects unsupported descriptors. [Canonical composite types and proof-bounded layouts](docs/development/composite-types.md) are implemented as the foundation for aggregate execution, which remains in progress.

```sh
lake build
lake exe nightlean check examples/PrivateClaim.lean
lake exe nightlean compile examples/PrivateClaim.lean --output build/claim
npm ci --prefix scripts/zkir
node scripts/zkir/verify.mjs build/claim/claimRelation.zkir
```

Compilation emits `claimRelation.zkir`, `PrivateClaim.claim.zkir`, `PrivateClaim.claim.impact.json`, and `nightlean.json`. The runtime plan describes witness visibility, the state schema, and native operations. Native artifact assembly uses Midnight's ledger APIs and actual ledger parameters for transcript partitioning and gas budgeting. [Native integration evidence](docs/development/native-localnet.md) records the exact tested boundaries. Full compiler assurance and public-network qualification remain separate work.

Follow the [source-driven native workflow](docs/development/native-contract.md) to generate keys, supply witnesses, prove, and submit a local contract call. The [independent toolchain guide](docs/development/native-toolchain.md) builds the pinned upstream ZKIR CLI without another source-language compiler.

The [Rust runtime and C ABI](docs/development/native-runtime-abi.md) execute without Node. The [native assembler](docs/development/native-assembler.md) consumes retained bytes from a [verified public bundle](docs/development/portable-artifacts.md), keeping private invocation files separate. The localnet harness still uses Node for development orchestration and receipt observation. Native toolkit steps supply funding, proving and submission.

Lean source and imported modules are trusted executable development inputs. Nightlean restricts the circuit DSL, but does not sandbox Lean elaborators or imported metaprograms. The CLI runs through the pinned Lake/Lean toolchain from the repository root.

The first implementation target is current Midnight ledger 9. Its first end-to-end workload is a private one-time claim: private eligibility data and Merkle path, public root and claim data, a proof relation, a derived nullifier, and ledger state that rejects reuse.

This workload sets the first delivery boundary. It does not define Nightlean's permanent language model. Nightlean's core will represent circuit relations and contract state transitions separately, with explicit private witnesses, public inputs, outputs, constraints, state reads, and state writes. The IR and target profile must support adding ledger-backed capabilities beyond this claim without redesigning around claim-specific operations.

Supported features follow Midnight's ledger and proving interfaces, then require a verified path through proving and contract execution. Nightlean has no Compact source backend or Compact runtime dependency. Historical adapter experiments remain documented as superseded evidence.

The public [Wayfinder map](https://github.com/awjreynolds/nightlean/issues/1) links the decisions, research, vertical-slice investigation, and implementation backlog. Evidence reports live in [`docs/research/`](docs/research/). [Moriarty](https://github.com/CharlesHoskinson/Moriarty) is a reference for ZKIR work, not a required compiler component or Nightlean language model.

Nightlean uses the MIT License.
