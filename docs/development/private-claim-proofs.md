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

Kernel replay, transitive axiom policy, trusted statement matching and exact source/build/deployment provenance are distinct audit requirements. The shell script establishes source theorem checking and source-mutation regressions. The separate audit check below binds the actual source policy to its checked proof statements. Neither check issues an authenticated build/deployment certificate.

The non-vacuity fixture is an explicit abstract-model instance. Its constant-zero hash oracle makes all four equations true and the actual circuit/entrypoint succeeds before replay rejection. A second successful fixture uses different secrets, siblings and directions while retaining the same declared public values, and instantiates the two-run observation theorem. This is deliberately not a qualified Poseidon implementation or native cryptographic evidence. The generic progress theorem instead accepts any canonical hash trace, including one supplied by the qualified target implementation once that correspondence is established.

## Remaining assurance bridge

The current theorems prove the stated source-semantic properties. They do not prove that emitted ZKIR constraints and Impact operations preserve these semantics, that an arbitrary satisfying native witness has the same source meaning, or that generated keys and the deployed verifier implement the proved relation. Native receipts and conformance tests provide separate evidence for selected executions.

Required follow-on work includes compiler/lowering soundness, canonical state/encoding correspondence, a formal target hash specification and explicit cryptographic assumptions, native prover/verifier and ledger assumptions, registered business specifications, non-vacuity policy, full axiom/statement checks and immutable proof-to-artifact/deployment binding. Membership and authorization claims must state the modeled eligibility tree and their cryptographic assumptions. The full correctness goal stays open until those obligations are met.


## Actual-source policy and export audit

`proofs/PrivateClaimVerification.lean` binds `Noctium.PrivateClaimVerification.policy` to the imported actual `PrivateClaim` contract and entrypoint index zero. Its `functional` and `privacy` theorems have the exact `FunctionalObligation policy` and `PrivacyObligation policy` types. Both register through the source proof registry. Their direct transitive axiom reports contain only `propext`, `Classical.choice` and `Quot.sound`.

The reviewed predicates separate accepted-execution safety from progress:

- `initial` describes canonical configured root/campaign values and an empty spent map. `checked_initializer` independently connects the existing checked initializer to this state.
- `invariant` describes the canonical configured cells and a map of unique canonical keys marked true.
- Broad `precondition` fixes the field modulus and requires the exact declared typed input environment with canonical values and domain tags. It does not assume a valid path, a correct nullifier, matching configuration, absence of the key or circuit/entrypoint acceptance.
- `enabled` supplies the four explicit `HashTrace` equations, matching configured public parameters and an absent nullifier. Those conditions establish progress. Nonvacuity uses the explicitly labeled constant-zero abstract hash model.
- `postcondition` derives configuration matches and absence from successful actual entrypoint execution. It requires reconstruction of the supplied root and nullifier, exact returned nullifier and recorded successor state, plus rejection of a repeated execution. The functional obligation also preserves the invariant.

`accepted_authorized` proves the backward safety step. Missing configuration guards or the absence check invalidate this reasoning. Eligibility is not hidden inside broad Pre. Hash equations for progress are explicit context assumptions, with no cryptographic injectivity or hiding assumption.

The privacy obligation uses the API's actual declared public input projection. Equal root, campaign and supplied nullifier, together with identical context and complete initial public state, imply equal successful source outcomes. Its release policy is `none`, meaning no additional release beyond those already declared public inputs. Its scope is `successfulOnly`, so failure observations are excluded. This theorem does not prove hiding of the public hashes, zero knowledge of native proof bytes, timing independence, provider privacy or compiler preservation.

Run fresh source compilation, proof export, kernel replay, direct axiom checks and exact-policy audit:

```sh
python3 scripts/proofs/check-private-claim-audit.py
```

The script compiles the actual source and both proof modules into a temporary import directory. Source filenames stay relative to the repository. It retains model/proof NDJSON bytes, the SHA256 pin, direct axiom reports, checker JSON and negative-test evidence under `.noctium/audits/private-claim-source/`. It supplies the retained model hash separately to `audit-source-proof.py`. The trusted checker starts from an empty environment, replays the exported kernel terms, checks the exact obligation types and rejects any changed declaration shared with the pinned model.

The default run treats its fresh baseline as trusted for this regression only. It does not authenticate a human specification review. After reviewing and retaining a model export, supply its independently recorded pin explicitly:

```sh
python3 scripts/proofs/check-private-claim-audit.py \
  --trusted-model-export /path/to/reviewed-model.ndjson \
  --trusted-model-sha256 <independently-recorded-sha256> \
  --output-dir /path/to/audit-evidence
```

The regression rejects the actual functional proof against a different policy with a weakened postcondition. It also freshly compiles a source mutation removing the root guard, deliberately pairs the changed relation with stale proof objects and requires `model_declaration_mismatch`. This tests source identity in addition to the six semantic proof-sensitivity mutations. No source files in the checkout change during either regression. The wrong-policy negative runs with the default baseline, which explicitly retains the generated test policy.

A successful audit reports `sourceFunctionalChecked: true`, `sourcePrivacyChecked: true` and `compiledContractVerified: false`. `specificationReviewVerified` and `sourceAuthorizationCorrespondenceProved` stay false. This is checked registration of an exact source statement and source contract, with scoped privacy. Emitted ZKIR/Impact preservation, target hash correspondence, verifier/key identity and deployed artifact binding remain separate open obligations.
