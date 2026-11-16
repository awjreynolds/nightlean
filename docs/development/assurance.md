# Compiler assurance status

Checked 2026-11-16. This report tracks [Establish semantic-preservation and backend conformance checks](https://github.com/awjreynolds/nightlean/issues/21). The ticket remains open because the backend transformations and external ledger boundary are not fully proved.

## Kernel-checked compiler transformation

`Nightlean.Passes.pruneCircuit` removes only constraints of the form `Expr.bool true`. It leaves inputs, outputs, source locations, other constraints, and their order unchanged. `pruneEntrypoint` applies this transformation to its circuit while preserving every state effect.

Lean checks these complete equality statements without added axioms or `sorry`:

- `pruneCircuit_validate`: validation returns the same result, including the exact first diagnostic and source span, for every capability profile and circuit.
- `pruneCircuit_run`: the executable reference evaluator returns the same result for every circuit, environment, and evaluation context. Equality includes missing or invalid inputs, noncanonical field values, constraint errors, hash-oracle errors, and named outputs.
- `pruneEntrypoint_validate`: contract-entrypoint validation is unchanged for every state schema and capability profile.
- `pruneEntrypoint_run`: the reference transition returns the same outputs and successor state, or the same error, for every initial state and environment.

The proof does not assume a particular Poseidon implementation, successful witness evaluation, or a valid input program. Two recursive helpers make source-order validation and execution explicit. They preserve the earlier evaluator's diagnostics and failure order. Tests cover successful output, empty constraints, missing inputs, unknown references, false-before-hash failure, and a reached hash-oracle error.

The native ZKIR lowerer applies the proven pass before relation and entrypoint lowering. The proof covers the pass's reference semantics. It does not prove the remaining ZKIR lowering correct.

## Current differential evidence

The [native backend spike](backend-spike.md) records official ZKIR 3.2.0 checking, native key generation, and a 3,852-byte proof for the actual two-level claim relation. The proof server performs native cryptographic self-verification. Altering the secret, sibling, direction, root, or nullifier caused direct assertion failure. Native CPU hash values and emitted circuit relations have finite conformance checks. These checks do not establish equivalence for every field value or source program.

The [direct Impact conformance harness](direct-impact.md) checks the Lean-generated native transcript with the ledger package and official ZKIR preprocessor. It rejects wrong witnesses, mismatched public or stored state values, and replay. The corrected direct transcript fixture has k=9, a 2,610-byte binary circuit, one activity group per VM operation, and the mandatory call communication commitment. The [source-driven native run](native-localnet.md) uses actual ledger parameters and the official transcript partitioner, and records finalized deployment and claim acceptance plus invalid-input and replay checks. This is finite execution evidence, not a compiler correspondence proof.

The earlier [local contract receipts](localnet-receipts.json) describe a historical packaging experiment. That backend has been removed. Current acceptance must use the native route and its own exact source, key, transaction, and receipt evidence. Public-network qualification remains separate.

## Actual contract proofs and source auditing

The [private-claim proof package](private-claim-proofs.md) imports the actual contract and proves its source eligibility equations, state transition, invariant preservation, framing and replay rejection. Its hash trace is an explicit oracle specification. It does not establish Poseidon secrecy, collision resistance or independently modeled tree membership. Six valid source mutations each fail the expected semantic proof clause.

The [proof-registration API](proof-registration.md) separates initialization, accepted-run correctness, enabled progress and non-vacuity. Privacy has its own obligation, based on canonical public inputs, public state and an explicit release policy. The current claim theorem compares successful executions. Failure behavior, proof bytes, host logs and timing are separate observables.

Fresh-kernel auditing authenticates a separately supplied trusted model digest, replays data-only Lean exports, matches exact expected obligation types and walks checked declaration bodies for transitive axioms. Only the pinned foundational `propext`, `Classical.choice` and `Quot.sound` identities are allowed. An admitted theorem, user axiom or native-computation axiom rejects. Kernel replay alone would accept derivations relative to those axioms, so replay is not the axiom policy.

Checked fixtures demonstrate the limits. A contract with an intentional private-value release is functionally correct but fails no-release privacy. A retained private unsigned subtraction passes the scalar disclosure checker and successful-only privacy, but its underflow exposes success versus failure and refutes all-outcomes privacy. Audit reports expose the exact scope, precondition, enabled condition and release definition.

These checks establish source-only guarantees. Independently reviewed specification pins, immutable source/import/build provenance, native lowering preservation, exact-byte certificates and deployed key/entrypoint binding form separate mandatory gates. Current reports keep `compiledContractVerified` and `specificationReviewVerified` false. No documented proof gap waives a required release proof.

## Unproved compiler and external boundaries

The following work remains before claiming full semantic preservation:

- Prove the ZKIR operation mapping, Native arithmetic and boolean representation, output/public-input binding, and witness ordering against a model of the accepted target semantics.
- Prove common-subexpression elimination preserves the generated circuit and transcript. Its current implementation uses serialized operation keys and exact input references. It is exercised by the native conformance fixtures, but has no Lean proof.
- Prove the native Impact plan, field encodings, state layout, guards, and writes match the reference transition, including failure atomicity.
- Prove the native runtime plan materialization and ledger-parameter budgeting preserve the Lean state-transition semantics. Native acceptance experiments are recorded separately from formal correspondence.
- Preserve the scoped source privacy theorem through native public inputs, state, activity groups and communication commitments. Extend obligations as events, calls, structured control and additional types become supported.
- Bind actual contract proof exports and reviewed policies to exact source/import/build identities, generated circuit/plan bytes, native keys and deployed entrypoints.
- Review the external checker, prover, verifier, proof-server serialization, and ledger execution boundaries. Existing upstream formalization does not cover every current ZKIR instruction, as recorded in the [source capability audit](../research/midnight-zkir-capability-matrix.md).
- Complete independent security review before a production-readiness claim.

Lean's kernel checks the stated internal theorems. It does not verify the Rust, JavaScript, WASM, Docker services, upstream cryptography, or public ledger in this project. No end-to-end formal-verification claim is made.

## Reproduce the internal checks

```sh
lake build
lake env lean tests/Passes.lean
lake env lean tests/IR.lean
lake env lean tests/Claim.lean
lake env lean tests/Frontend.lean
lake env lean tests/ScalarPolicy.lean
lake env lean tests/Disclosure.lean
bash tests/cli.sh
bash tests/uint-cli.sh
bash tests/disclosure-cli.sh
bash scripts/proofs/check-private-claim.sh
python3 scripts/proofs/check-private-claim-audit.py
python3 scripts/proofs/check-registration.py
```

The external conformance commands, exact versions, and artifact limits remain in their linked reports so each piece of evidence stays tied to its own target boundary.
