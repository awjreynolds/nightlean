# Lean proofs and the contract audit chain

Research checked on 2026-11-16. The proof baseline is immutable Nightlean commit `bfda641375c8b2e67d43b71f112833794ec72a55`. Lean is pinned to 4.35.0. The installed binary reports source commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`. Concurrent implementation changes were excluded from baseline conclusions. This report changes no compiler or runtime code.

Proof-backed functional correctness should be a required release property. A successful Lean build, a named theorem, a native proof receipt and a bundle hash each establish different facts. The required chain joins a reviewed specification to the exact source contract, its transformations, emitted ZKIR/Impact bytes, keys and deployed operation. No existing result establishes this entire chain.

## Verified baseline and tools

An isolated source export of the pinned Nightlean commit built `Nightlean.Passes` and `Nightlean.Claim` successfully using `lake build Nightlean.Passes Nightlean.Claim`. The experiment ran outside the repository at `/private/tmp/nightlean-proof-baseline-bfda641`. All 18 theorem declarations in ScalarPolicy, Semantics, Passes and Claim were inspected with `#print axioms`.

| Existing proof | Established fact | Missing link |
| --- | --- | --- |
| ScalarPolicy's six theorems | Inclusive bounds, arithmetic ranges, widening and exclusive-bound conversion | Correctness of every typed operation, serializer and native lowering |
| Semantics.pruneTrue_preserves | Literal-true pruning preserves a constraint satisfaction predicate | Native circuit behavior |
| Semantics.unsigned_addition_no_wrap and unsigned_multiplication_no_wrap | Natural results equal field results under explicit bounds | Every emitted instruction implements those arithmetic relations |
| Semantics.unsigned_underflow_outside_range and unsigned_underflow_modulo_rejected | Underflow lies outside the permitted unsigned range | The emitted range check exists and enforces the correct bound |
| Passes' six theorems | The implemented pruning pass preserves validation and executable circuit/entrypoint evaluation, including errors | Correctness of Impact/ZKIR lowering and serialization |
| Claim.marked_isSpent | The separate markSpent function makes isSpent true | Successful Claim.contract execution uses the same update, preserves unrelated state and rejects a second claim |

The first five ScalarPolicy theorems have no axiom dependencies. `exclusive_addition_maximum` uses `propext` and `Quot.sound`. The Semantics results use `propext`, with `Quot.sound` also appearing in the underflow results. All six Passes results use `propext` and `Quot.sound`. `Claim.marked_isSpent` also uses `Classical.choice`. These are observed dependencies, not a requirement to eliminate ordinary classical reasoning. Sources: [ScalarPolicy](https://github.com/awjreynolds/nightlean/blob/bfda641375c8b2e67d43b71f112833794ec72a55/Nightlean/ScalarPolicy.lean), [Semantics](https://github.com/awjreynolds/nightlean/blob/bfda641375c8b2e67d43b71f112833794ec72a55/Nightlean/Semantics.lean), [Passes](https://github.com/awjreynolds/nightlean/blob/bfda641375c8b2e67d43b71f112833794ec72a55/Nightlean/Passes.lean), [Claim](https://github.com/awjreynolds/nightlean/blob/bfda641375c8b2e67d43b71f112833794ec72a55/Nightlean/Claim.lean).

The existing semantics parameterizes Poseidon through `EvalContext.poseidon2`. An arbitrary supplied oracle is not a proof of the native hash implementation or its cryptographic properties. `runEffects` describes tentative state and returns no successor on error. This proves neither external callback rollback nor native ledger atomicity. The claim builder and the surface example are distinct declarations. A theorem about `Claim.contract` does not automatically cover `examples/PrivateClaim.lean`.

The installed toolchain contains `leanchecker` and `leanexport`. These concrete commands were executed successfully:

```sh
lake env lean BaselineAxioms.lean
lake env leanexport Nightlean.Passes Nightlean.Claim -- \
  Nightlean.Passes.pruneEntrypoint_run \
  Nightlean.Claim.marked_isSpent \
  Nightlean.unsigned_underflow_modulo_rejected > baseline-proof-closure.ndjson
lake env leanchecker --from-export baseline-proof-closure.ndjson
lake env leanchecker --fresh Nightlean.Claim
```

The exported dependency closure contains 118,156 NDJSON records and 6,140,307 bytes. SHA-256: `39bd26f973fc5eb352f8933633770f64cc34912a61c4ef29d4437529bdf4da88`. Replay returned exit 0 and reported acceptance by the default Lean kernel. The fresh-module replay also completed with exit 0. This verifies those declarations relative to their axioms. It does not verify the full compiler.

Pinned source also supports `lake env leanchecker --fresh Module.Name`, which replays the module's imported constant closure into a fresh environment. Without `--fresh`, module replay starts from the imported environment. The export reader supplies a useful boundary between elaboration and checking. These tools use Lean's kernel, so they are not independent kernel implementations. The older separate lean4checker repository is deprecated because this tooling moved into Lean. Sources: [LeanChecker](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/LeanChecker.lean), [LeanExport entrypoint](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/LeanExport.lean), [export writer](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/LeanExport/Basic.lean), [migration notice](https://github.com/leanprover/lean4checker#readme).

Do not substitute an invented recheck flag or rely on the broad wording of `lean --trust=0` help. The pinned Shell passes a trust level into the frontend. Environment import constructs maps from serialized declarations. Explicit declaration replay is implemented by LeanChecker/Replay. Use the verified replay route as a separate gate. Sources: [Shell](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Shell.lean), [Environment.finalizeImport](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Environment.lean#L2308), [Replay](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Replay.lean).

## Axiom inspection is a separate mandatory gate

Lean 4.35 exposes `Lean.collectAxioms` and `#print axioms declaration`. The collector traverses declaration types and bodies, including opaque/theorem bodies. Imported declarations use precomputed axiom metadata exported with their modules. This is convenient during a controlled build. It is not independent verification of hostile imported metadata. Independently inspect the exported dependency closure and exact axiom declarations in the audit process. Sources: [CollectAxioms](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Util/CollectAxioms.lean), [print command](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Elab/Print.lean#L293).

A scratch experiment reproduced these outcomes:

| Proof construction | Reported dependency |
| --- | --- |
| `by decide` for 2 + 2 = 4 | None |
| `by native_decide` for the same equality | A generated `native._native.native_decide.ax_1_1` axiom |
| A theorem using a user axiom of False | The user axiom |
| `by sorry` | `sorryAx` |
| `by admit` | `sorryAx` |

The probe compiled with warnings for sorry/admit and exit 0. Exporting the last four constructions and running `leanchecker --from-export` also returned exit 0. This is expected: the kernel checks proofs relative to declared axioms. Acceptance alone does not establish an acceptable assumption set. The probe stayed under `/private/tmp/nightlean-proof-audit-435` and introduced no repository axiom.

In this Lean version, native evaluation creates a new axiom for each asserted computation. Searching only for historical names such as `Lean.trustCompiler` or `Lean.ofReduceBool` is insufficient. `native_decide` and `decide +native` share this path. The native helper also underlies uses by other tactics, including `bv_decide`. Inspect the resulting proof dependencies, not a blacklist of tactic spellings. Ordinary `decide` and `decide +kernel` construct proofs checked through reduction. Sources: [native evaluation](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Meta/Native.lean#L30), [Decide](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Elab/Tactic/Decide.lean).

Recommended release rule: allow the reviewed foundational `propext`, `Classical.choice` and `Quot.sound` identities with their pinned declarations. Reject every other transitive axiom for a required correctness obligation, including generated native-computation axioms, sorry, admit and user-added axioms. A name-only allowlist is insufficient if a definition/environment was substituted. Compare expected declarations and dependencies against the trusted foundational/specification environment.

Model-specific assumptions should appear as explicit, reviewed theorem parameters. They must not silently enter through a global axiom. A theorem conditional on native relation soundness or collision resistance remains conditional, even with a clean axiom list. This default supports unrestricted theorem/tactic/library authoring. A proof tactic is accepted when its resulting term meets the release policy. Authors remain free to experiment with native evaluation, then replace or discharge its computation obligations before release.

## Full Lean authoring and the finite circuit subset

Keep the full Lean proof language available for definitions, propositions, quantifiers, induction, dependent types, classical proofs, tactics and imported libraries. Proof terms are erased from runtime execution. Only computations selected for circuit extraction need finite target semantics. A proof about arbitrary natural numbers or inductive traces need not be representable as a circuit.

The trust boundary is the checked result, not a small approved tactic list. Elaborators, macros and tactics produce proof terms. Audit tools must also treat their build-time execution as untrusted code when supplied by an outside author. Build in a bounded isolated environment, export the relevant proof closure, and perform release checks in a separate trusted process. Do not run contract-supplied validation callbacks as the authority deciding whether their own proofs qualify.

Lean's official guidance distinguishes kernel replay, axiom review and trusted theorem-statement comparison. It also describes comparator and independent checkers. Those external workflows were not installed or qualified here. The exact installed `leanexport`/Lean kernel replay path was exercised. A future independent checker is additional assurance, not a fictional completed gate. Source: [official proof-validation guidance](https://lean-lang.org/doc/reference/latest/ValidatingProofs/). This guidance is a moving reference. Version-specific behavior above comes from the pinned 4.35 source.

## The required assurance chain

| Link | Required evidence | Current status |
| --- | --- | --- |
| Reviewed intent to formal specification | Human-readable pre/postconditions, invariants, failure behavior and explicit assumptions | No complete private-claim specification package |
| Specification to exact source contract | Checked theorem whose type mentions the actual contract definition and semantics version | Only the separate marked_isSpent lemma |
| Source transformations | Semantic preservation theorem for each applied pass and checked composition | Literal-true pruning proved |
| Source contract to target relation/Impact semantics | Soundness and appropriate completeness/error-preservation theorems for supported lowering | Missing |
| Target model to emitted bytes | Checked decode/encode correspondence and exact-artifact certificate | Missing |
| Circuit/plan to key material | Verified identities, pinned key-generation provenance and native key/circuit agreement | Hash/schema checks and native operational evidence, no general proof |
| Key/plan to deployed contract operation | Authenticated deployment state binds network, address, operation and verifier key | Requires an explicit audit receipt linked to the proof bundle |
| Accepted transaction to specified behavior | Composition of the preceding theorems with stated native/prover/ledger assumptions | Missing |

For the circuit relation, prove both the sound direction needed for security and a completeness direction needed for usability. Native satisfaction must imply source acceptance, and valid source executions must admit the required target execution under explicit oracle and representation assumptions. A one-way theorem with an impossible target relation would make every claim reject and still satisfy soundness.

For ordered state effects, preserve read values, state schema identities, operation order, failure conditions and final state. Relate source state to the actual Impact state representation. Bind opcode groups, skip/activity structure, alignments, key paths, read results and write values to the proof's public transcript. The current lowerer explicitly treats opcode grouping and communications commitment as relevant. These are theorem obligations, not metadata details. Sources: [Impact lowering](https://github.com/awjreynolds/nightlean/blob/bfda641375c8b2e67d43b71f112833794ec72a55/Nightlean/Backend/Impact.lean), [ZKIR lowering](https://github.com/awjreynolds/nightlean/blob/bfda641375c8b2e67d43b71f112833794ec72a55/Nightlean/Backend/Zkir.lean).

The current compiler obtains registered circuits/contracts through unsafe `evalConstCheck`. Even a proved Lean lowering function does not prove its native execution or the bytes written by an executable. Close this boundary with a checked artifact certificate: the decoded emitted bytes equal the target object related by the preservation theorem to the exact registered contract. A proof-producing translation validator with a proved soundness theorem is an acceptable implementation route. A Boolean validator evaluated through native_decide would reintroduce the compiler trust axiom. Source: [Compiler registration and emission](https://github.com/awjreynolds/nightlean/blob/bfda641375c8b2e67d43b71f112833794ec72a55/Nightlean/Compiler.lean).

Existing public bundles establish selected-file integrity and schema associations against an authenticated external digest. Their documentation expressly excludes semantic equivalence, build attestations and deployed-key agreement. Extend this format, rather than relabel its existing hash checks as proof preservation. Source: [portable artifact boundary](../development/portable-artifacts.md).

## Registration and an audit-readable proof bundle

Introduce a typed registration interface in a trusted Nightlean module. This is a proposed interface, not an existing command. A registration supplies an actual proof term checked against an expected obligation such as `ContractCorrect semantics contract specification`, together with required invariant, initialization and progress obligations. A theorem name string alone never satisfies registration.

The expected type must reference the actual elaborated contract constant. Compare its declaration body and semantic dependency closure to the object compiled. The hand-built `Claim.contract` and the generated example need a proved correspondence or one shared definition. Contract names, entrypoint names and source-file hashes do not establish this equality.

Use a versioned proof manifest with these fields:

| Group | Required data |
| --- | --- |
| Identity | Contract declaration, entrypoint, source revision/tree digest, canonical source-IR identity, target profile and specification ID/version |
| Obligations | Role, theorem declaration, full instantiated proposition, proof-export digest, semantic model IDs and exact contract/specification arguments |
| Dependencies | Exported declaration closure, axiom identities and types, explicit assumptions, imported module/library revisions, source and build-product hashes |
| Transformations | Ordered applied passes, preservation theorem instances, target relation/Impact model IDs, serializer/decoder correspondence |
| Artifacts | Exact ZKIR, Impact plan, schemas, parameters and prover/verifier key digests, plus native key-generation provenance |
| Audit reproduction | Lean/checker versions and executable digests, lockfiles, build options, relevant environment settings, replay commands and structured results |
| Deployment | Network/genesis identity, contract address, operation/entrypoint, accepted verifier-key identity, initialization state and authenticated chain reference |
| Review | Plain-language guarantee, excluded observables, specification-review decision and proof-policy version |

Keep theorem statements and referenced definitions readable in the bundle. Include source locations, raw exported terms and a dependency graph. Pretty printing is for auditors. Machine identity must not depend on custom notation, an untrusted pretty printer or unstable display text. The proof export digest identifies the checked serialized closure, not the runtime artifact by implication.

The import closure needs both source provenance and build-product provenance. Pin Lean, Lake dependencies, library revisions and lockfiles. Include relevant `.olean` parts and dynamic/IR build artifacts in the reproducible build record. Rebuild the project closure from immutable sources in isolation. Record whether the Lean toolchain/core libraries were rebuilt or accepted as distribution binaries. A path on LEAN_PATH and an imported .olean's claimed module name do not authenticate its source. Exported declaration checking reduces dependence on elaboration code but still requires an audited parser, kernel, trusted statement and foundational environment. Sources: [import implementation](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/Lean/Environment.lean), [checker module-part loading](https://github.com/leanprover/lean4/blob/eb6cafb7290e8bd5f2937522d8d804f58f02bafc/src/LeanChecker.lean#L17).

The deployment join must authenticate the operation's actual verifier key and initialization state. Recording a key filename is insufficient. Hashing a key and circuit separately is also insufficient to prove the key was generated for the intended circuit. Bind those identities through the qualified native generation/verification interface and its stated trust assumptions. Treat upgrades as a new deployed revision with a new proof/key binding, even if the contract address remains unchanged.

## First proved private-claim contract

Write the claim specification independently of the implementation's update helper. Its inputs should identify a canonical state relation, campaign, accepted root, supplied nullifier, private secret, fixed-length sibling path and direction bits. State canonicality must address duplicate cell/map names, key equality, correct field types, canonical values and the representation invariant for spent entries. List lookup's first-match behavior is not an adequate substitute for a well-formed ledger-state invariant.

Required properties:

1. Initialization establishes the canonical state invariant and the selected root/campaign.
2. Successful execution implies the witness leaf/path reconstructs the accepted root and the supplied nullifier equals the designated domain-separated hash of secret/campaign.
3. Success implies the accepted root and campaign match state, the nullifier was absent, and the successor marks precisely that nullifier spent while preserving unrelated fields and keys.
4. The state invariant survives success. Repeating the same nullifier against that successor fails without a successor state in the model.
5. A canonical, valid witness with an absent nullifier succeeds, provided the modeled hash calls succeed. This is the progress/nonvacuity theorem.
6. Every failure returns no model successor. Separately establish the native transaction's rejection/atomicity boundary.
7. The actual generated source contract and emitted artifacts satisfy these obligations through the preservation chain.

The Merkle relation proves existence of a satisfying path. It does not, by itself, prove knowledge extraction, membership in a separately constructed tree under adversarial hash collisions, campaign entitlement or secrecy. Any such statement needs its own definitions and cryptographic assumptions. Nullifier collision resistance and the proof system's soundness/zero-knowledge properties are explicit external assumptions unless separately formalized. Domain tags 1/2/3 are application choices in this contract.

Nonvacuity needs more than a passing sample. The general progress theorem covers valid witnesses. A concrete admissible instance supplies a readable demonstration. Neither establishes the intended policy if the specification accidentally permits an unrelated user to claim. Review quantifier order, preconditions, state framing, authorization and the meaning of “private.” Data/control disclosure checks and their soundness are additional obligations, not consequences of functional correctness.

## Bounded next packages

These are implementation/proof packages, not claims of completed assurance. Existing source feature work continues in parallel. Proof registration is mandatory for audited release, not an optional annotation.

| Package | Bounded scope and dependencies | Required exit evidence |
| --- | --- | --- |
| PA-01, theorem registration and axiom policy | Typed proof registration for one contract/entrypoint. Trusted expected proposition, contract identity and approved foundational declarations. Depends on current typed IR and artifact schema | Reject unknown theorem, wrong contract/specification, theorem of True, sorry/admit, user axiom and per-native-computation axiom. Accept the current legitimate proofs. Mutated spec definitions with unchanged names reject. Exported closure replays |
| PC-01, source claim transition correctness | Canonical state relation, initialization, success/frame/invariant/replay and progress theorems for the actual claim definition. Tie generated example to the proved definition. Reuse marked_isSpent only through a proved bridge | Kernel proofs for all seven properties above within source semantics, explicit hash assumptions, valid-instance witness and rejection fixtures. Changed spent update, skipped absent check, wrong campaign/root or swapped path direction must break an obligation |
| PL-01, claim scalar/Boolean/hash target relation | Typed semantics for the pinned native subset used by the claim. Prove expression lowering soundness/completeness and composition with pruning. Treat hash implementation equivalence as a named assumption initially | Bool canonicality, field arithmetic, equality, select and domain-separated hash obligations. Reject omitted constraint or altered direction wiring. Native checker/prover tests qualify model agreement but do not replace the theorem |
| PL-02, claim Impact/state and transcript preservation | Relate current cell reads, requirements, absent-map check and insertion to native state/Impact semantics, including operation grouping and public binding. Depends on PC-01/PL-01 and the native assembly schema | State correspondence and ordered-effect theorem, transcript relation theorem, replay-rejection theorem. Tampered slot/path/key/value/read/opcode group fails certificate or native validation. Isolated-ledger positive and replay cases provide implementation evidence |
| PA-02, exact-artifact certificates and proof bundle | Connect canonical decoding of exact ZKIR/Impact bytes to the proved source contract and pass chain. Export proof/specification closure and build/import provenance. Depends on PA-01/PL-01/PL-02 and existing bundling | Rebuild immutable source, replay certificates, enforce axiom policy, compare trusted obligations. Changed bytes, theorem body, import product, source contract or target profile invalidate the binding. No receipt-only preservation claim |
| PA-03, key/deployment audit join | Authenticate qualified key generation and actual deployed operation against the proof bundle. Depends on PA-02 and native assembly/deployment interfaces | Wrong key, address, entrypoint, parameters, network, initialization or revision rejects. Retain a public audit bundle with authenticated deployment reference and explicit native/crypto assumptions |

PA-01 and PC-01 should start immediately. PC-01 supplies the first contract-specific theorem rather than more disconnected library lemmas. PL-01 and PL-02 make that theorem relevant to the running claim. PA-02 and PA-03 close the artifact and deployment identity chain. A source-only theorem earns a precise source-level claim during development. It does not satisfy the final contract release requirement.

No native backend opcode should later enter a proof-qualified release without a source rule, target semantics, lowering/validation obligation, privacy rule and artifact identity path. Shared compiler theorems then scale across contracts and the full pinned native feature set. Full Lean audit authoring remains unrestricted.

## Trust gaps to retain explicitly

The baseline has no general proof of lowering, byte serialization, runtime/witness-plan conformance, key generation or native ledger acceptance. The claim policy lemma is not yet a transition theorem. No independent kernel implementation was qualified in this research. Replay uses the installed Lean kernel and trusts its logic, executable and platform. The installed binary's reported commit is provenance evidence, not a verified bootstrap theorem.

The final guarantee remains conditional on the pinned native implementations matching their formal models, proof-system and hash assumptions, correct parameter/key generation, authenticated ledger observations and relevant host behavior. A provider is an untrusted witness source for proof validity, but its external effects, secret handling and persistence need separate runtime guarantees. Failure/timing leakage is outside an ordinary functional transition theorem.

Tests, proof receipts and local-ledger results remain valuable evidence about those implementation assumptions. They never replace a universally quantified preservation proof. Each audit bundle must make the boundary visible in its guarantee statement and required obligation list.

