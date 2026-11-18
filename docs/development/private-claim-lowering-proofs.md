# Private-claim native relation proofs

The actual private-claim circuit now has kernel-checked soundness and completeness against an independently defined native scalar/Boolean/hash relation. Soundness covers every satisfying internal SSA assignment, including assignments never produced by the evaluator. Completeness covers arbitrary canonical eligible source inputs and, separately, any successful source execution with correct native Boolean encodings.

The separate [native state/transcript package](private-claim-native-state-proofs.md) now proves the actual ledger call's formal state preservation and decoded plan/call binding.

This package qualifies the standalone `claimRelation.zkir` scalar relation. It does not establish the contract-call relation's state/Impact execution semantics, authenticated compiler builds, exact byte parsing, keys or deployed ledger identity. `compiledContractVerified` stays false.

## Independent model and source binding

`Noctium/Verification/NativeRelation.lean` defines canonical BLS12-381 scalars as `Fin Field.modulus`, typed operands, instruction constraints and ordered observations. An SSA witness is an arbitrary function from names to canonical scalars. It is not a source evaluation result, a `NativeExpected` normalization or a compiler-generated witness by definition.

`CircuitSatisfies` requires every instruction constraint, the exact ordered public/private input streams and the exact ordered public Impact groups. `Satisfies` additionally records host output observations. The distinction matters: upstream standalone `Output` appends host outputs but does not add a public proof instance when communications commitment is disabled. The actual claim's final Impact group independently authenticates its returned nullifier. The strongest soundness theorem assumes only `CircuitSatisfies` and derives the actual return's equality to that final public group.

The actual circuit uses public root/campaign/nullifier inputs, five private field inputs, two Boolean constraints, four hash instructions, four selections, two equality tests and assertions, four Impact groups and one Output, totaling 27 instructions. The literal target program in `proofs/PrivateClaimLowering.lean` states this graph independently. Its repeated leaf/node SSA uses account for common-subexpression sharing. Each defining equation must hold for any satisfying witness. No generic CSE or arbitrary-expression compiler theorem is claimed.

The proof imports `proofs/PrivateClaim.lean`, which imports the actual `examples/PrivateClaim.lean` contract. `source_circuit_identity` proves its selected entrypoint circuit equals the actual standalone `claimRelation` declaration. The existing source-expression/hash-trace theorems refer to those actual source constraints. Thus native path/hash equations are connected to the source relation rather than to a duplicate source evaluator.

The target's assertion semantics follows the pinned circuit implementation: Assert requires nonzero, not exact one. TestEq itself constrains its result to zero/one. Their combination therefore proves equality for arbitrary internal witnesses. Both explicit direction constraints and selection require Boolean selectors. Canonical field types rule out alternative noncanonical field representatives. Scalar add/mul/neg helper semantics exist in the model, but the claim's lowering proof qualifies only its actual instruction graph, which contains no arithmetic instructions.

## Main theorem statements

| Theorem | Established property |
| --- | --- |
| `native_constraints_sound` | For any canonical input streams and arbitrary satisfying native SSA assignment, the actual source circuit accepts the decoded source inputs, returns the supplied nullifier, and its native return equals the final public Impact group. No host-return assertion is a premise |
| `native_satisfaction_sound` | Also identifies all four public groups, observed return values and native direction canonicality |
| `native_constraints_pruned_sound` | Composes soundness with the existing proved pruning pass, including the actual source circuit's executable semantics |
| `source_acceptance_complete` | Any successful actual source circuit execution with native zero/one direction encodings admits a satisfying native assignment |
| `eligible_source_complete` | Canonical source fields plus independent path/nullifier hash equations admit a satisfying native assignment, using the proved source eligibility theorem |
| `decoded_constraints_sound` | Lifts the arbitrary-witness theorem to an independently decoded JSON tree with an exact checked target-program certificate |
| `decoded_eligible_constraints_complete` | Lifts source completeness to the same certified JSON tree |
| `fixture_native_nonvacuity` | Supplies an explicit abstract-model native satisfying witness. Its constant-zero oracle is labeled as a model fixture, not native Poseidon evidence |

`compute` and `computedWitness` occur in the completeness construction only. The security direction quantifies over every satisfying assignment. The completeness proof first derives native calculated root/nullifier values from actual successful source expression checks, then constructs an assignment satisfying the native constraints. It never assumes native satisfaction as an eligibility premise.

## Hash and implementation assumptions

`HashAgreement ctx hash` is an explicit theorem parameter. It fixes the source modulus to the native scalar modulus and equates each source `poseidon2 domain left right` call on canonical fields with the native hash function applied to the ordered three-field vector `[domain, left, right]`. This assumes neither source acceptance nor compiler soundness. Intermediate native hash values are canonical by their scalar type.

The generic theorems hold for every hash satisfying this agreement. They assume no hash injectivity, collision resistance, hiding, Merkle knowledge extraction or proof-system zero knowledge. Real native acceptance implies satisfaction of this formal instruction model only under the separately qualified native implementation and proof-system soundness assumptions. This package does not prove the native Poseidon gadget or Rust implementation in Lean.

The pinned implementation is ZKIR revision `7a51b3385bbf4bce3604df87a7c70867c9ab43c0`, selected release 3.2.1, IR language 3.2. The instruction behavior was checked against its [`ir_vm.rs`](https://github.com/midnightntwrk/midnight-zkir/blob/7a51b3385bbf4bce3604df87a7c70867c9ab43c0/zkir/src/ir_vm.rs): selector Boolean conversion and true/false arms, equality gadget results, Native-vector transient hashing, nonzero circuit assertions and Output/Impact handling. The implementation's preprocessing assertion checks exact Boolean one, which is stronger than its isolated circuit Assert gadget. The universal model uses the circuit condition.

## Fresh JSON-tree certificate and checks

`NativeRelationJson.decode` checks the exact root fields, IR 3.2 header, empty root input signature, Native output types, communication flag and per-op fields. It preserves instruction order, input visibility, operands, output names and Impact grouping. It accepts canonical minimal little-endian field immediates and rejects unsupported opcodes/types/input guards. Impact guards must be literal one. Inactive or variable-guard Impact semantics need a later package.

Run:

```sh
python3 scripts/proofs/check-private-claim-lowering.py
```

The script builds the Lean model/decoder and CLI, checks focused decoder tests, builds the actual source and proof modules in a fresh temporary import directory and compiles the actual source through the selected 3.2.1 target. Source/proof module filenames stay relative to the repository. No example/proof object files enter the checkout.

The emitted JSON bytes are retained and parsed into a candidate literal JSON tree. The quotation input rejects duplicate keys, nonfinite/floating/exponent numbers and negative integer spellings. A fresh Lean certificate proves `decode emittedJson = .ok program` through ordinary `decide +kernel` and checked equality reasoning. It specializes both native soundness and completeness to that tree. This is kernel computation, with no native computation axiom. The generator supplies only a candidate term, not an acceptance verdict.

The certificate covers the quoted JSON tree. Correspondence between original UTF-8 bytes and that tree, parser semantics, an authenticated build and source/import provenance remain in the exact-artifact package. Lean's existing JSON parser uses opaque partial implementation details, so this check does not relabel runtime parsing as a kernel byte-decoding theorem.

Two valid native tree mutations must fail their checked certificate: swapping the first selector's arms and removing the root assertion. Module/import errors do not count. The regression requires an error at the actual kernel equality check. It exports the relevant proof/certificate closure, inspects actual exported axiom declarations and safe-definition flags, then replays the closure using `leanchecker --from-export`.

A public [qualification summary](../../tests/private-claim-lowering-evidence.json) records the checked theorem/certificate export and native fixture observations. Retained development evidence lives under `.noctium/audits/private-claim-lowering/`. The current source SHA256 is `5a2e0f2f8b087567d00a274bc64bfb893b4ddf70fb459923ccd2db05be1bf771`. The fresh standalone artifact SHA256 is `c3a8c9aad701302d54e630961ff159a97e5957e699ae6fc14cc7d5aa78d3395c`. The checked export is about 38 MiB. All required theorem and certificate dependencies use only `propext`, `Classical.choice` and `Quot.sound`. Export hashes are recorded per run. These development hashes are not an authenticated release certificate.

## Native model qualification

Use the pinned official checker separately from the proofs:

```sh
node tests/private-claim-lowering-checker.mjs \
  /path/to/official-3.2.1/midnight_zkir_wasm_fs.js \
  .noctium/audits/private-claim-lowering/emitted/claimRelation.zkir
```

An optional third argument points to the matching native CLI. It generates fresh keys and requests a standalone proof from the existing loopback proof server at `127.0.0.1:16300`, which verifies before returning success. This submits no ledger transaction.

Nine measured checker vectors cover a valid claim, changed direction, non-Boolean direction, wrong root, wrong nullifier, wrong final public Impact, and the two structural mutants. The missing-root-assert mutant accepts an incorrect root. The swapped-selector mutant rejects the original relation's witness and accepts a witness for its changed relation. Those observations demonstrate real semantic sensitivity rather than malformed-input rejection.

The development fixture uses secret 42, campaign 9, siblings 17/23 and directions 0/1. Native qualification generated and self-verified a 3,852-byte standalone proof. Checker/prover JSON records retain the exact field values, artifact/tool hashes and proof digest. No native test samples arbitrary malicious internal assignments. The universally quantified Lean theorems provide that model-level coverage. Key provenance, deployed verification, state semantics and cryptographic privacy remain separate obligations.
