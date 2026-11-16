# Nightlean

Nightlean is a Lean 4 compiler project for Midnight contracts. Its source elaboration, typed intermediate representation, reference semantics, and ZKIR relation lowering are implemented in Lean.

The active goal is [verified feature equivalence](docs/compatibility/GOAL.md) with a pinned Compact capability baseline, through Lean-to-ZKIR and native ledger execution. The current implementation is a private-claim POC. A host-neutral runtime, broader language coverage and full equivalence evidence are in progress.

The compilation path is Lean source → typed circuit and contract IR → ZKIR v3 and native Impact runtime plans → Midnight proving and ledger libraries. The compiler emits standalone circuit relations, native entrypoint relations, and typed runtime metadata. The selected POC target is an isolated ledger 9 localnet.

The actual private-claim source completed native deployment at finalized block 398 and a valid claim at block 401. Wrong secret, path, direction, root, and nullifier are rejected. Replay leaves state unchanged. [Native receipts and provenance](docs/development/native-localnet.md) record the tested source, independent ZKIR toolchain, keys, and transactions.

```sh
lake build
lake exe nightlean check examples/PrivateClaim.lean
lake exe nightlean compile examples/PrivateClaim.lean --output build/claim
npm ci --prefix scripts/zkir
node scripts/zkir/verify.mjs build/claim/claimRelation.zkir
```

Compilation emits `claimRelation.zkir`, `PrivateClaim.claim.zkir`, `PrivateClaim.claim.impact.json`, and `nightlean.json`. The runtime plan describes witness visibility, the state schema, and native operations. Native artifact assembly uses Midnight's ledger APIs and actual ledger parameters for transcript partitioning and gas budgeting. [Native integration evidence](docs/development/native-localnet.md) records the exact tested boundaries. Full compiler assurance and public-network qualification remain separate work.

Follow the [source-driven native workflow](docs/development/native-contract.md) to generate keys, supply witnesses, prove, and submit a local contract call. The [independent toolchain guide](docs/development/native-toolchain.md) builds the pinned upstream ZKIR CLI without another source-language compiler.

Lean source and imported modules are trusted executable development inputs. Nightlean restricts the circuit DSL, but does not sandbox Lean elaborators or imported metaprograms. The CLI runs through the pinned Lake/Lean toolchain from the repository root.

The first implementation target is current Midnight ledger 9. Its first end-to-end workload is a private one-time claim: private eligibility data and Merkle path, public root and claim data, a proof relation, a derived nullifier, and ledger state that rejects reuse.

This workload sets the first delivery boundary. It does not define Nightlean's permanent language model. Nightlean's core will represent circuit relations and contract state transitions separately, with explicit private witnesses, public inputs, outputs, constraints, state reads, and state writes. The IR and target profile must support adding ledger-backed capabilities beyond this claim without redesigning around claim-specific operations.

Supported features follow Midnight's ledger and proving interfaces, then require a verified path through proving and contract execution. Nightlean has no Compact source backend or Compact runtime dependency. Historical adapter experiments remain documented as superseded evidence.

The public [Wayfinder map](https://github.com/awjreynolds/nightlean/issues/1) links the decisions, research, vertical-slice investigation, and implementation backlog. Evidence reports live in [`docs/research/`](docs/research/). [Moriarty](https://github.com/CharlesHoskinson/Moriarty) is a reference for ZKIR work, not a required compiler component or Nightlean language model.

Nightlean uses the MIT License.
