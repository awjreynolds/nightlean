# Nightlean

Nightlean is a Lean 4 compiler project for Midnight contracts. Its source elaboration, typed intermediate representation, reference semantics, and ZKIR relation lowering are implemented in Lean.

The current compiler checks restricted contract and circuit declarations, emits ZKIR v3 relations, and describes contract state effects in separate metadata. The emitted metadata marks the bundle as unqualified and nondeployable until ledger transcript integration is complete. The public Wayfinder map tracks the remaining proof and deployment work.

The private one-time claim has completed deployment and a finalized call on an isolated ledger 9 development chain through the optional Lean-generated packaging adapter. Five invalid-claim cases and nullifier replay leave ledger state unchanged. [Localnet evidence](docs/development/localnet-claim.md) and [independent finalized receipts](docs/development/localnet-receipts.json) record the exact transactions. Preview qualification is pending and is tracked separately.

```sh
lake build
lake exe nightlean check examples/PrivateClaim.lean
lake exe nightlean compile examples/PrivateClaim.lean --output build/claim
npm ci --prefix scripts/zkir
node scripts/zkir/verify.mjs build/claim/claimRelation.zkir
```

Use `--adapter compact` with `compile` to emit the bounded packaging source alongside direct ZKIR. The official Compact toolchain then builds that source into runtime bindings and keys. This adapter has localnet evidence for the implemented claim. The direct native transcript backend has [VM and preprocessing conformance evidence](docs/development/direct-impact.md), with direct contract transaction integration still open.

Lean source and imported modules are trusted executable development inputs. Nightlean restricts the circuit DSL, but does not sandbox Lean elaborators or imported metaprograms. The CLI runs through the pinned Lake/Lean toolchain from the repository root.

The first implementation target is current Midnight ledger 9. Its first end-to-end workload is a private one-time claim: private eligibility data and Merkle path, public root and claim data, a proof relation, a derived nullifier, and ledger state that rejects reuse.

This workload sets the first delivery boundary. It does not define Nightlean's permanent language model. Nightlean's core will represent circuit relations and contract state transitions separately, with explicit private witnesses, public inputs, outputs, constraints, state reads, and state writes. The IR and target profile must support adding ledger-backed capabilities beyond this claim without redesigning around claim-specific operations.

Compact does not define Nightlean's source semantics or feature boundary. A Compact adapter remains an optional way to package selected programs when it preserves Nightlean's semantics. Supported features follow Midnight's ledger and proving interfaces, then require a verified path through proving and contract execution.

The public [Wayfinder map](https://github.com/awjreynolds/nightlean/issues/1) links the decisions, research, vertical-slice investigation, and implementation backlog. Evidence reports live in [`docs/research/`](docs/research/). [Moriarty](https://github.com/CharlesHoskinson/Moriarty) is a reference for ZKIR work, not a required compiler component or Nightlean language model.

Nightlean uses the MIT License.
