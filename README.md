# Nightlean

Nightlean is a Lean 4 compiler project for Midnight contracts. The compiler, source elaboration, typed intermediate representation, and primary lowering will be implemented in Lean.

The repository is still in planning. No compiler modules have been implemented. The public Wayfinder map and its linked research and implementation tickets are ready for the next implementation pass.

The first implementation target is current Midnight ledger 9. Its first end-to-end workload is a private one-time claim: private eligibility data and Merkle path, public root and claim data, a proof relation, a derived nullifier, and ledger state that rejects reuse.

This workload sets the first delivery boundary. It does not define Nightlean's permanent language model. Nightlean's core will represent circuit relations and contract state transitions separately, with explicit private witnesses, public inputs, outputs, constraints, state reads, and state writes. The IR and target profile must support adding ledger-backed capabilities beyond this claim without redesigning around claim-specific operations.

Compact does not define Nightlean's source semantics or feature boundary. A Compact adapter remains an optional way to package selected programs when it preserves Nightlean's semantics. Supported features follow Midnight's ledger and proving interfaces, then require a verified path through proving and contract execution.

The public [Wayfinder map](https://github.com/awjreynolds/nightlean/issues/1) links the decisions, research, vertical-slice investigation, and implementation backlog. Evidence reports live in [`docs/research/`](docs/research/). [Moriarty](https://github.com/CharlesHoskinson/Moriarty) is a reference for ZKIR work, not a required compiler component or Nightlean language model.

Nightlean uses the MIT License.
