# Exact PrivateClaim artifact certificates

This package joins the actual PrivateClaim source/specification proofs, native scalar/state/privacy proofs and exact public artifact bytes. It uses a total Lean byte decoder and a proof-producing translation validator. Python never supplies an authoritative parsed JSON tree. A separate data checker reads the retained files, constructs their byte literals and compares those literals with the exported certificate constants through the Lean kernel.

The qualified subject remains the actual claim: its 27-instruction standalone relation, 55-instruction native call, 21-operation state plan and selected target profile. This is not a whole-language compiler theorem. The normal compiler gains no permanent ASCII, JSON or artifact-size feature ceiling from these claim-specific qualification limits.

Qualification status: the implementation is at a provisional checkpoint. Core parser and exact-byte/data-checker prototypes have passed. The immutable published-source authority/candidate qualification is still pending. No authenticated build receipt is claimed yet.

Key/deployed-operation identity remains issue 57. Native implementation, parser and cryptographic assumptions remain explicit. No unqualified verified-contract label follows from this package. `compiledContractVerified` stays false.

## Exact byte semantics

`Nightlean/Verification/ArtifactBytes.lean` defines `Bytes := List UInt8` and a total, fuel-bounded parser. No UTF-8 conversion or whitespace normalization precedes parsing. The accepted qualification subset is:

- At most 65,536 bytes and 64 nested containers.
- Objects, arrays, strings, booleans, null and minimal nonnegative decimal UInt64 integers.
- The four JSON whitespace bytes: space, tab, LF and CR.
- ASCII strings, standard JSON escapes and ASCII-valued four-digit Unicode escapes.

The parser rejects duplicate decoded keys, leading-zero numbers, overflow, fractions, exponent notation, negative numbers, trailing commas, incomplete input, trailing garbage, unescaped controls, BOMs and unsupported non-ASCII strings. Escaped aliases of the same object key also count as duplicates. These restrictions describe the current certificate subset, not every JSON document accepted by Rust or every future source-language feature.

`validated_tree` proves that a successful downstream validator yields both exact parsing and the expected typed target decoding. The selected JSON tree is derived from the Lean parser itself. It is not an externally quoted AST.

`ArtifactCertificate.decodeProgram`, `decodePlan` and `decodeProfile` compose this parser with the independently defined native relation/state decoders and an exact selected-profile decoder. The latter records every target package version and the pinned native source revision. Actual field values continue to use the canonical little-endian scalar encoding checked by the existing native relation decoder.

A generated per-artifact certificate proves these decoder equalities through `decide +kernel`. Its source contains raw byte literals and typed build identities. It uses no native evaluation axiom, unsafe evaluator, `native_decide` or `evalConstCheck` acceptance shortcut.

This establishes serializer/decoder correspondence for the exact retained serializer outputs. The validator checks bytes after emission, so compiler serialization is an untrusted producer. No generic correctness theorem for Lean.Json.pretty or every compiler serialization is claimed. The existing compiler's internal evaluation mechanism does not confer certificate authority.

## Source, native state and privacy composition

`proofs/PrivateClaimArtifacts.lean` defines `Certified` for the actual standalone, plan, call and profile byte streams. The generated proof binds:

- Exact native target programs and state operations.
- The selected target profile and exact profile bytes.
- The actual source/specification/role identities from the reviewed model closure.
- An externally authenticated build identity and its exact expected artifact bytes.

`FunctionalPreservation` specializes issue 55's arbitrary-assignment/VM-trace theorem to the parsed byte trees. Source acceptance and the exact successor are derived. `EligibleCompleteness` specializes its source-to-native progress theorem. Actual native gas/size admission remains an explicit implementation requirement.

`exact_byte_build_binding` constructs the concrete `NativePrivacy.ExactArtifactBinding` interface supplied by child issue 63. `concrete_privacy` then instantiates the native two-run privacy obligation for those byte trees. Its observer and scope remain unchanged: successful valid executions, equal declared public inputs and canonical public state/context, coupled host coins/public parent context, and explicit agreement for the final bound proof statement. Proof bytes, failures, timing, provider access and logs remain excluded.

The exact-byte checker verifies source functional, source privacy and separate native privacy roles. It also checks the generated concrete binding, functional preservation, completeness and privacy theorem types. A functional theorem cannot substitute for a privacy proof.

## External authority, not candidate self-certification

A kernel theorem cannot read a Git server, authenticate a filesystem build or prove its own bootstrap executable. `Authenticated` therefore means equality to an externally supplied expected authority. The independent checker matches the entire authority value against a separately pinned input, including exact artifact bytes. The authority is not inferred from a candidate manifest, and its predicate is not a self-declared True.

The public controller separates four steps:

1. Measure an immutable full source commit in isolation. This produces measurements only, with no authority status.
2. An independent reviewer or release authority checks the source/model/toolchain/profile identities and supplies the expected measurement-file SHA256 outside the candidate.
3. Prepare the authority through another fresh source build using those external pins.
4. Rebuild a candidate independently, require complete product/artifact equality, then run the trusted data/kernel checker in a separate process.

The authority records the immutable commit/tree, public source closure, exact policy names, base theorem/dependency export, reviewed model export, Lean/compiler/checker/toolchain identities, profile bytes, imported build products and compiler product. Its expected generated certificate export digest is stored outside the Lean build record to avoid a self-hash cycle.

Both builds must start with fresh output directories. The source closure and actual source files are checked, not merely claimed source digests. Imported products are checked both in the retained product collection and at the paths loaded by the trusted checker. Toolchain measurement covers executable identities, shared libraries and installed Lean object/IR products. The current checker/controller/helper source must match the published source revision.

The independent data process imports only trusted checker code and authenticated products. Candidate modules and initializers are never imported. It parses data exports, compares declarations against the independently pinned model, replays terms in a fresh kernel, enforces the transitive axiom allowlist and checks exact required statements. Only `propext`, `Classical.choice` and `Quot.sound` qualify.

`AuditArtifactExport.lean` constructs a `List UInt8` term directly from each separately read retained file. `Kernel.check` and `Kernel.isDefEq` compare this term with the exported byte constant. Every byte matters, including whitespace. The checker also compares against the independent authority's retained files. It does not rely solely on an AST equality or a candidate-supplied hash label.

The Lean sub-check is one component of the protocol. It expects its authority/model inputs to have passed the controller's external-pin and provenance checks. Calling that component with an arbitrary self-selected authority is not authenticated build qualification.

## Commands

After publishing and reviewing the core implementation, measure its immutable full commit:

```sh
python3 scripts/proofs/check-private-claim-artifacts.py measure \
  --trusted-source-commit FULL_PUBLISHED_COMMIT \
  --output-dir /private/tmp/claim-measurement
```

An independent authority must check and pin the resulting inputs. Measurement output alone grants no trust. Then rebuild the authority:

```sh
python3 scripts/proofs/check-private-claim-artifacts.py prepare-authority \
  --trust-input /path/to/independently-reviewed-measurements.json \
  --trust-input-sha256 EXTERNALLY_SUPPLIED_SHA256 \
  --output-dir /private/tmp/claim-authority
```

Use the externally supplied authority-file digest for candidate creation and independent checking:

```sh
python3 scripts/proofs/check-private-claim-artifacts.py build-candidate \
  --authority /private/tmp/claim-authority/authority.json \
  --authority-sha256 EXTERNALLY_SUPPLIED_AUTHORITY_SHA256 \
  --bundle /private/tmp/claim-candidate

python3 scripts/proofs/check-private-claim-artifacts.py verify \
  --authority /private/tmp/claim-authority/authority.json \
  --authority-sha256 EXTERNALLY_SUPPLIED_AUTHORITY_SHA256 \
  --bundle /private/tmp/claim-candidate
```

Public builds accept no invocation configuration or private witness input. This pipeline performs no proof-service request, transaction submission or deployment.

## Negative checks and native parser samples

The `regress` command takes the same authority/bundle arguments as `verify`. It changes retained bytes, whitespace, source definitions, specification text, theorem bodies, imported build products, selected profile and exported certificate bytes. Every change invalidates the old binding.

A dedicated kernel sub-check must reject changed whitespace even when the earlier hash-manifest gate is deliberately bypassed. A fresh whitespace variant still passes the parsing/model equality, showing the rejection binds exact bytes rather than confusing whitespace with malformed JSON. A valid semantic instruction mutation must fail at the actual kernel decoding equality. Import or setup failures never count as semantic rejection evidence.

`native-agreement --bundle ... --cargo /path/to/cargo --native-checker /path/to/official-3.2.1/midnight_zkir_wasm_fs.js` runs the separate Rust serde_json 1.0.154 probe and official ZKIR parser samples. Accepted samples include whitespace, escapes, UInt64 bounds, nesting and the actual public artifacts. Official parsing checks whitespace and ASCII-escape variants of the actual standalone/call artifacts.

Those samples qualify implementation agreement for the retained subset. They are not proofs of Rust, serde_json, the native parser or the complete JSON language. `NativeParserAgreement` names the finite-artifact implementation assumption explicitly.

## Remaining trust and scope

The report retains an honest business-specification review flag. Technical kernel replay does not review whether the user's intended eligibility policy is correct. The current pipeline records that review as unverified.

The trusted bootstrap includes the selected Lean kernel/checker binaries, toolchain/object integrity, Python/filesystem/hash/process operations, host OS/linker/SDK behavior, Git/source identity and authenticity of the external authority pins. Native parser/VM/hash/proof-system agreement remains separate. None of these implementation assumptions is converted into a new global Lean axiom or a false claim of verified bootstrap.

Issue 57 still needs to join this bundle to authenticated key generation and the actual deployed network/address/entrypoint/verification operation. This package certifies no deployed ledger identity and grants no blanket confidentiality or whole-compiler assurance.
