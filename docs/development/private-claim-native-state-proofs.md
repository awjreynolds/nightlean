# PrivateClaim native state and public transcript proofs

The actual `examples/PrivateClaim.lean` claim now has kernel-checked state preservation against an independent native stack machine. The security direction quantifies over arbitrary satisfying assignments for the actual 55-instruction call and arbitrary checked VM traces for the actual 21-operation plan. The VM does not invoke source `run`, compiler lowering, runtime `prepare`, or an assumed honest read provider.

This package closes the claim-specific formal state/transcript link. Exact UTF-8 byte parsing and authenticated compiler/import builds remain issue 56. Key/deployment identity remains issue 57. `compiledContractVerified` stays false. Source assurance 21 requires every remaining link before reporting a compiled-contract guarantee.

## Independent native model

`Nightlean/Verification/NativeState.lean` defines canonical scalar cells with field or one-byte Boolean alignment, native array/map nodes, a stack machine, exact read observations and an independently checked trace relation. The qualified state shape is a root array containing two field cells followed by one field-keyed map. The model represents maps as entry lists. A well-formed source invariant supplies unique keys, canonical keys and true spent markers. The preservation theorem also holds for the larger abstract list domain.

The machine implements the claim's push, popeq, dup, index, member and insert operations. Popeq compares the complete aligned cell against the actual top of stack. Membership tests key presence, including entries whose stored value is false. Path-preserving index retains the parent array and its field-aligned index on the stack. Insert 2 first rebuilds the map at the supplied key, then rebuilds the root array at the saved index. Missing paths, wrong slots, type/alignment mismatches and incorrect expected reads return no model successor. Transient/storage flags survive in the opcode transcript. The model abstracts native reference-strength bookkeeping, whose implementation agreement is an explicit boundary.

`Trace` admits only successful step equations, and `trace_iff_run` proves equivalence to the executable VM. A trace starting from another state or reporting fabricated reads does not satisfy this relation. Canonical source/native encodings are stated through `sourceValues`, `encodedEntries`, `mark_encoding`, `encoded_mark` and `absence_encoding`.

## Actual program and ordered statement

`proofs/PrivateClaimNativeState.lean` independently specifies the actual ledger-call instruction list and VM plan. `actual_schema_order` and `actual_effect_order` bind the proof to the imported source declaration, including state names, slot order, cell types, map types and every ordered effect.

The plan contains these 21 operations:

1. Three field push/popeq pairs echo root, campaign and supplied nullifier.
2. Dup/index slot 0/popeq reads acceptedRoot.
3. Dup/index slot 1/popeq reads campaignId.
4. Dup/index slot 2/push nullifier/member/bit-aligned popeq false checks absence.
5. Index slot 2 with saved path/push nullifier/storage push one/insert 2 records the claim.

The call contains the shared 22 scalar/hash instructions, three additional public reads, a Boolean constraint on membership, three test-equality/assert pairs, 21 Impact groups, one storage-value select and an empty Output. Its communications-commitment flag is true. `scalar_projection` proves the actual call's arbitrary satisfying assignment satisfies the previously proved standalone scalar relation. No scalar evaluator result is assumed in the security direction.

`groups_encoding` proves equality between the call's ordered public groups and the independent VM's field representation. Group boundaries, opcode values, index paths, alignments, storage flags and write values survive this equality. The relation supports only literal-one active Impact guards. There are no skipped groups or jumps in this claim. `Execution` couples the checked trace, public groups and actual Popeq read values to the call's six ordered public-input scalars.

`PublicStatement` and `Accepted` additionally bind the all-active mask, public read values, communication commitment and explicit admission budget. Empty contract input/output communication uses an explicit native commitment oracle with its randomness. The commitment equation is a primitive relation premise, not a proved cryptographic property or a claim about a deployed proof verifier. This matches the pinned implementation's separate communication-commitment check for the empty input/output vector.

## Checked theorem scope

| Theorem | Property |
| --- | --- |
| `execute_plan` | Exact success/failure characterization for arbitrary public fields, configured cells, expected reads, map entries and replacement value |
| `native_execution_sound` | Arbitrary call satisfaction and VM trace imply configured root/campaign equality, absent nullifier and the exact native successor/read stream |
| `source_native_preservation` | The imported source entrypoint accepts and reaches exactly the state encoded by that native successor |
| `eligible_native_complete` | Arbitrary canonical eligible source inputs with an absent key admit a 55-instruction satisfying assignment and a checked 21-op VM trace with matching reads/groups |
| `eligible_admitted_complete` | The same completeness under explicit operation and map-entry bounds, including the public statement and communication equation |
| `public_transcript_preserved` | Ordered opcode groups, exact six reads, all-active mask and empty communication commitment agree with execution |
| `native_replay_rejected` | A second execution for the inserted key has no native successor, regardless of the attempted replacement write |
| `entries_frame`, `native_frame` | Every other map key and both configured root cells retain their values |
| `invariant_preserved` | The source/native spent-state encoding preserves the existing canonical state invariant |
| `decoded_execution_sound`, `decoded_execution_complete` | The same preservation and completeness specialize to independently decoded plan/call JSON trees through checked certificates |

The source/hash agreement parameter remains the one from the scalar package. No hash injectivity, collision resistance, knowledge extraction, privacy, zero knowledge or native proof-system soundness theorem is introduced here.

## Fresh artifacts and negative checks

Run the formal package:

```sh
python3 scripts/proofs/check-private-claim-state.py
```

Add local pinned native implementation qualification:

```sh
python3 scripts/proofs/check-private-claim-state.py \
  --native-checker /path/to/official-3.2.1/midnight_zkir_wasm_fs.js
```

The script builds the actual source/proofs in a fresh temporary import directory, compiles the actual example through the selected 3.2.1 target and retains the emitted plan/call bytes. It quotes independently parsed candidate JSON trees, then uses ordinary `decide +kernel` and checked equality reasoning to certify both decodings. The candidate generator supplies no acceptance verdict. Duplicate keys, nonfinite/floating/exponent numbers and negative integer spellings are rejected by the quotation parser inherited from the scalar package.

`NativeStateJson.decode` checks the semantic plan fields, exact top-level field set, schema, ordered read declarations, guards, contract/entrypoint/call identity and each supported operation/expression field. Its fuel-bounded structural JSON comparison avoids Lean.Json's opaque partial equality implementation. Descriptive circuit metadata and the nested target profile are carried as JSON, outside the semantic projection. Their provenance belongs to the authenticated-build boundary. The call decoder checks every native instruction and root field as in the scalar package.

Ten mutations must fail at the actual kernel equality check: wrong slot, saved path, key, write value, expected read, alignment, storage flag, read declaration order, opcode grouping and inactive group. Import failures or missing identifiers do not qualify as rejection evidence. The script exports 15 proof roots and four fresh certificate roots, rejects all non-approved transitive axiom declarations and unsafe definitions, then replays the exported closure with `leanchecker --from-export`.

Development evidence lives under `.nightlean/audits/private-claim-state/`. A portable summary is retained in `tests/private-claim-state-evidence.json`. Exact byte-to-tree correspondence is not claimed. The proof does not treat a runtime JSON parse, CLI exit code, hash or local-ledger sample as a kernel byte certificate.

## Native implementation and admission boundary

The model was checked against pinned ZKIR revision `7a51b3385bbf4bce3604df87a7c70867c9ab43c0`, selected release 3.2.1, and the ledger APIs consumed by the native assembly flow. Native acceptance implies the formal relation only under implementation agreement for canonical field/Boolean encoding, aligned values, map key equality, VM stack/path/insertion rules, Impact field representation, activity handling, read comparison and the empty communication commitment. Rust/Wasm memory management, persistence, reference strength, gas accounting and proof-system internals are not proved in Lean.

The admission predicate bounds 21 operations and the prior map length plus the inserted entry. It does not claim those symbolic units equal a ledger gas limit. Applying the general completeness theorem to native ledger acceptance requires sufficient real cost, size and memory limits for the encoded state and these operations. The finite native sample uses initial ledger parameters. It is evidence for that sample only.

`tests/private-claim-state-checker.mjs` consumes the fresh actual plan/call, obtains six reads by executing native QueryContext, checks the official 3.2.1 call relation, replays the native transcript, checks both configured cells, checks the new key and an unrelated key, and rejects replay plus wrong configured root/campaign and a present key with false value. Eight transcript mutations reject in the official relation checker. All 21 native activity entries report active.

The sample also invokes native `PreTranscript` and `partitionTranscripts`, the interfaces used by `runtime/src/assembly.rs`. Partitioning preserves the exact 21-op sequence and reaches the same successor. Initial parameters allocate all 21 operations to the guaranteed transcript. Production construction separately requires the assembly path to preserve this order, use the same context/state/entrypoint, bind the same public/private streams, and carry the same empty input/output commitment and randomness through `ContractCallPrototype`. The existing assembly implementation checks its real preimage with the official checker. This package does not relabel that Rust path as a proved compiler or deployment certificate.
