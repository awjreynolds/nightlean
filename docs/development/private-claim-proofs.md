# Private-claim source semantic proofs

`proofs/PrivateClaim.lean` imports the actual `examples/PrivateClaim.lean` contract and proves properties of its executable Lean semantics. The proofs refer to the imported entrypoint. They do not substitute the policy-only `Claim.marked_isSpent` lemma for a contract execution theorem.

Run the local checks from the repository:

```sh
bash scripts/proofs/check-private-claim.sh
```

The script builds the Lean library, compiles the actual example into a new temporary import directory and checks the proof module. Source filenames stay relative to the repository, preserving stable source-span metadata. It writes no example/proof `.olean` files into the checkout. It then checks six valid source mutations in isolated temporary directories. Each must compile as a contract, then fail its corresponding semantic proof clause. An import or module-load error does not satisfy the regression.

| Source mutation | Required failing proof clause |
| --- | --- |
| Remove the root guard | `wrong_root_effects_rejected` |
| Remove the campaign guard | `wrong_campaign_effects_rejected` |
| Change the nullifier domain | `source_constraints` |
| Remove nullifier recording | `effects_accept_unspent` |
| Remove the absent-nullifier check | `effects_reject_recorded` |
| Reverse the first path direction wiring | `source_constraints` |

## Specification

The model state contains the configured root and campaign cells plus a spent-nullifier map. A valid reachable map has unique canonical field keys, each marked true. Initial state has an empty map.

`InputValues` provides the three public field values, secret, two siblings and two Boolean directions. `CanonicalInputs` requires field values below the context modulus and valid domain tags. `HashTrace` separately states four hash equations: leaf domain 1, two directional path nodes using domain 2, and nullifier domain 3. Intermediate leaf/node values must also be canonical. The context's hash function remains an explicit parameter.

These hypotheses describe computations the contract requires. They do not assert hash injectivity, collision resistance or membership in an independently modeled eligibility tree. The source expression equalities and source constraints are bound by a kernel-checked `source_constraints` theorem, so changing those constraints breaks the proof.

## Proved properties

| Theorem | Claim |
| --- | --- |
| `hash_trace_circuit_accepts` | Canonical inputs and the separately stated hash/path/nullifier equations establish acceptance by the actual circuit. Circuit acceptance is proved here, rather than assumed |
| `successful_source_root_and_nullifier` and `successful_contract_root_and_nullifier` | Successful actual circuit or entrypoint execution on canonical inputs reconstructs the supplied root and computes the supplied domain-separated nullifier |
| `eligible_claim_correct` | An unspent eligible invocation succeeds, records its nullifier, preserves the state invariant, preserves every other map lookup and rejects an actual replay execution |
| `recorded_preserves_cells` | The complete root/campaign cell list stays unchanged |
| `recorded_state_preserves_invariant` | Canonical keys, key uniqueness and true spent markers survive the transition |
| `checked_initializer` | The range-checked initializer returns the specified empty-map state for canonical root/campaign values |
| `wrong_root_claim_rejected` and `wrong_campaign_claim_rejected` | Even an accepted circuit cannot bypass the actual entrypoint's configured-root/campaign guards |
| `successful_public_observations_equal` | Two successful actual executions from the same unspent public state with equal declared public values return equal results and public state, even with different private witnesses |

`state_functional_correctness` exposes the state theorem separately, with actual circuit acceptance as an explicit premise. `eligible_claim_correct` discharges that premise using `HashTrace`. Replay rejection is an equation about a second call to the actual `Entrypoint.run`, including its disclosure and circuit checks. The theorem also applies to another accepted witness yielding the same nullifier under the stated configuration, because the replay lemma quantifies over its context and inputs.

The canonical state invariant is proved initially and after recording. A separate framing theorem preserves lookup results for every key other than the claimed nullifier. Rejected executions return an error without a successor state in this pure model. These proofs do not roll back arbitrary external host callbacks.

`PublicObservation` contains returned values and the complete current public `LedgerState`. The two-run theorem fixes the declared root, campaign and nullifier as authorized public values. It proves no additional dependence of successful public results/state on secret, siblings or directions. It excludes proof-byte distributions, timing, failure behavior, logs, provider traces and native transcript preservation. It does not prove that a public hash hides its input or that the chosen public-release policy matches business intent.

## Proof checking and assumptions

The proof module uses ordinary Lean theorem syntax, induction, simplification, arithmetic reasoning and kernel computation. It contains no `sorry`, `admit`, user axiom, `native_decide` or unsafe proof. Transitive axiom output for the main claims contains only the standard foundational axioms `propext`, `Classical.choice` and `Quot.sound`, or subsets of those names. The script prints the main dependency reports.

Kernel replay, transitive axiom policy, trusted statement matching and exact source/build/deployment provenance are distinct audit requirements. This local script establishes source theorem checking and source-mutation regressions. It does not issue an authenticated audit certificate or replace the required proof registry and artifact-binding work.

The non-vacuity fixture is an explicit abstract-model instance. Its constant-zero hash oracle makes all four equations true and the actual circuit/entrypoint succeeds before replay rejection. A second successful fixture uses different secrets, siblings and directions while retaining the same declared public values, and instantiates the two-run observation theorem. This is deliberately not a qualified Poseidon implementation or native cryptographic evidence. The generic progress theorem instead accepts any canonical hash trace, including one supplied by the qualified target implementation once that correspondence is established.

## Remaining assurance bridge

The current theorems prove the stated source-semantic properties. They do not prove that emitted ZKIR constraints and Impact operations preserve these semantics, that an arbitrary satisfying native witness has the same source meaning, or that generated keys and the deployed verifier implement the proved relation. Native receipts and conformance tests provide separate evidence for selected executions.

Required follow-on work includes compiler/lowering soundness, canonical state/encoding correspondence, a formal target hash specification and explicit cryptographic assumptions, native prover/verifier and ledger assumptions, registered business specifications, non-vacuity policy, full axiom/statement checks and immutable proof-to-artifact/deployment binding. Membership and authorization claims must state the modeled eligibility tree and their cryptographic assumptions. The full correctness goal stays open until those obligations are met.
