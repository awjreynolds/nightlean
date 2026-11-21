# Public entrypoint bundles

The native Rust `noctium-bundle` tool assembles and verifies a versioned public bundle for one contract entrypoint. Lean still implements compilation and primary lowering. Bundling neither invokes Compact nor executes the circuit, generates a proof or submits a transaction.

The default profile stays `midnight-ledger-9`: ledger 9.1.0.1 at `a2b30128ca4b660b73a068e29b56b48ede8c9a74`, native ZKIR 3.2.0 at `446c7fecc6bd41dab99ebe89ab404e9d077d11a9`, and Lean 4.35.0. The [selected 3.2.1 build](zkir-3.2.1-integrated.md) accepts its matching profile and source pins through the same manifest format. Each consumer rejects bundles for the other linked profile.

## Artifact stages

1. Lean compilation emits the circuit, symbolic Impact plan and `noctium.json` schemas. Compilation does not generate keys.
2. The pinned native ZKIR tool generates prover/verifier keys. Its build manifest records source, executable and lockfile identities.
3. The bundler selects public files, checks their associations and writes canonical manifest bytes. Private execution belongs outside this directory.

Required roles are explicit source files, native contract ZKIR, its `.impact.json` plan, compiler metadata, one ABI header/schema, target profile, public ledger parameters, prover key, verifier key and native tool provenance. Only source selections permit multiple entries. The recipe stays outside the bundle. File selection never recursively copies an input directory.

| Role | Bundle path |
| --- | --- |
| source | `source/<explicit logical source name>` |
| circuit | `circuit/entrypoint.zkir` |
| plan | `plan/entrypoint.impact.json` |
| metadata | `schema/noctium.json` |
| abi | `schema/noctium_runtime.h` or `schema/abi.schema.json` |
| profile | `profile/target.json` |
| ledgerParameters | `parameters/ledger.params` |
| proverKey, verifierKey | `keys/entrypoint.prover`, `keys/entrypoint.verifier` |
| toolchain | `provenance/native-zkir.json` |
| witnessBinding, optional pair | `witness/entrypoint.binding.json` |
| witnessControl, optional pair | `witness/entrypoint.control.json` |
| rustBinding, optional generated module | `bindings/rust/<selected module name>` |

Each manifest entry records its role, logical name, relative path, byte size and lowercase SHA-256. Logical circuit and plan names preserve the compiler's original filenames even though bundle paths are fixed. The selected plan must name the selected native circuit. Compiler metadata must agree on the contract, entrypoint, state schema, plan name and complete circuit schema. Target/component/source identities must match the supported profile. Public JSON artifacts reject unknown top-level fields.

When circuit outputs share an exact leading chain of local bindings, Impact plan schema 2 records it once as `circuit.sharedBindings`. The ordered `[name, value]` pairs run before the remaining output expressions, once per evaluation pass. The bindings stay local to the circuit. A missing private input defers dependent outputs. In constraint metadata, `sharedLets` expands to the same binding chain at its original lexical position. Plans without a shared prefix use schema 1. The native ZKIR and witness artifacts stay byte-identical.

A selected typed-witness entrypoint requires both optional witness roles. Their logical names preserve the compiler's `.witness.json` and `.witness.control.json` filenames. Verification checks the exact embedded sidecar bytes, source input and signature schemas, ordered fresh-input bindings, actual CALL relation and selected target identity. Unreferenced, incomplete or mismatched pairs reject. Existing bundles without typed witnesses retain the same canonical bytes. See [typed source witnesses](typed-witnesses.md).

## Select compiler outputs

```sh
lake exe noctium compile examples/PrivateStateCounter.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit witness --output build/private-counter
```

Repeat `--emit` to select artifact roles. The target profile still selects the ledger and ZKIR versions. The compiler checks the full source and emits the selected products into a new or empty directory.

| Compiler role | Files |
| --- | --- |
| `ledger` | Entrypoint `.zkir` and `.impact.json` |
| `standalone` | Standalone `.zkir` |
| `witness` | `.witness.json` and `.witness.control.json` for selected ledger or standalone relations |
| `control` | Host-only `.control.json` |
| `specialization` | `.specialization.json` |
| `observations` | `.observations.json` |

Ledger entrypoints with host witnesses require `--emit witness`. Without explicit roles the compiler emits all applicable files. An explicit selection adds an `artifacts` inventory to `noctium.json` with every emitted file and its role. Ledger exports without standalone circuits use compiler metadata schema 3. Each entrypoint records the SHA-256 of its minified Impact plan as `nativePlanSha256`. The plan holds the circuit schema, and the metadata's `circuits` array is empty. The Rust bundler checks the inventory and exact plan digest alongside the contract and witness associations. Other explicit selections use compiler metadata schema 2. The public bundle has its own version 1 manifest.

The witness files provide a language-neutral interface for the Rust runtime and C/C++ ABI. Add `--bindings rust` to generate Rust modules for the selected ledger witness entrypoints. Each module appears under `bindings/rust/` and has a `rustBinding` inventory entry with a SHA-256 of the exact emitted bytes, including the final newline. A bundle recipe may select one module as the `rustBinding` role. The bundler requires its path and basename to match the selected witness control file and checks its bytes against the compiler inventory digest. At a trusted manifest boundary, the manifest pin binds the included Rust source bytes to the compiler inventory. Rust module emission remains opt-in. [Generated Rust witness modules](typed-witnesses.md#generate-a-rust-witness-module)

## Build and use

Build the runtime with its pinned Rust toolchain and lockfile:

```sh
cargo build --manifest-path runtime/Cargo.toml --locked --bin noctium-bundle
cargo test --manifest-path runtime/Cargo.toml --locked --test artifacts
```

The local recipe uses schema version 1, a declared compiler Git revision and a file array. This example shows all required selections. Replace each `input` with the corresponding public input file, and use the exact revision of the compiler which produced the output.

```json
{
  "schemaVersion": 1,
  "compilerRevision": "0851aca03586164708981742e9e833c080897661",
  "files": [
    {"role":"source","name":"examples/PrivateClaim.lean","input":"examples/PrivateClaim.lean"},
    {"role":"circuit","name":"PrivateClaim.claim.zkir","input":"compiled/PrivateClaim.claim.zkir"},
    {"role":"plan","name":"PrivateClaim.claim.impact.json","input":"compiled/PrivateClaim.claim.impact.json"},
    {"role":"metadata","name":"noctium.json","input":"compiled/noctium.json"},
    {"role":"abi","name":"noctium_runtime.h","input":"runtime/include/noctium_runtime.h"},
    {"role":"profile","name":"target.json","input":"profiles/midnight-ledger-9.json"},
    {"role":"ledgerParameters","name":"ledger.params","input":"public/ledger.params"},
    {"role":"proverKey","name":"entrypoint.prover","input":"public/claim.prover"},
    {"role":"verifierKey","name":"entrypoint.verifier","input":"public/claim.verifier"},
    {"role":"toolchain","name":"native-zkir.json","input":"native-zkir/build-manifest.json"}
  ]
}
```

```sh
noctium-bundle assemble recipe.json new-public-bundle
noctium-bundle verify new-public-bundle TRUSTED_MANIFEST_SHA256
```

`assemble` requires a new output directory and reports `manifestSha256`. Input path strings never enter the manifest. Native provenance is normalized to public source/tool identities, hashes and build command. The local absolute `binary` path is removed. The verifier rejects changed or missing payloads, unsafe relative paths, path conflicts, symlinks and unlisted files/directories. Paths which differ only by case also conflict. Every shared directory prefix must use identical casing, so `Foo/A.lean` and `foo/B.lean` reject before the output directory is created. Exclusive file creation rejects additional aliases normalized by the host filesystem. Existing destinations are never overwritten. A failed write removes only the output directory created by that assembly attempt.

The verifier optionally accepts a trusted manifest digest, supplied through a separate trusted channel. Without this digest or another authentication scheme, verification establishes internal consistency only. An attacker who replaces both a payload and its unsigned manifest is not detected. Signing, release trust distribution and deployed-key agreement are separate work.

### Distribute without the prover key

```sh
noctium-bundle assemble-without-prover-key recipe.json new-public-bundle
```

Use the same recipe and native keys during release. This command writes the complete bundle's exact manifest and omits `keys/entrypoint.prover`. The manifest still commits to its size and SHA-256.

Rust clients load this variant with `artifacts::verify_and_regenerate(directory, trusted_manifest_sha256, finalized_state, parameters)`. Supply the finalized contract state for the intended address from your ledger state provider and the trusted proving parameters. The loader verifies all shipped payloads, selects the plan's operation in the supplied state and checks its installed V3 verifier. The pinned native library independently generates the key pair from the retained circuit and supplied parameters. The loader checks the resulting verifier and the exact committed prover-key bytes before returning an ordinary `VerifiedBundle` with the key in memory. Use that bundle through the normal Rust proving and composition APIs.

The normal `verify` command still requires every listed file. Regeneration writes no key to disk and reports a mismatch when the deployed verifier, regenerated verifier or committed prover key differs. Fetching finalized state and retaining the regenerated bundle across calls belong to the host. The browser and mobile loaders still require complete bundles.

Errors use JSON with stable `error.code` values, including `unsupported_version`, `unsupported_name`, `profile_mismatch`, `plan_mismatch`, `digest_mismatch`, `manifest_digest_mismatch`, `unsafe_path`, `private_artifact`, `missing_role` and `limit_exceeded`. Error messages omit input values and local paths.

## Canonical representation and limits

Manifest schema 1 uses UTF-8 compact JSON, object keys in ascending string order, unsigned decimal sizes, lowercase hexadecimal digests and one trailing LF. Entries follow the declared role order (`source`, `circuit`, `plan`, `metadata`, `abi`, `profile`, `ledgerParameters`, `proverKey`, `verifierKey`, `toolchain`, `witnessBinding`, `witnessControl`, `rustBinding`), then ascending logical name within a role. The verifier rejects alternate whitespace, unknown manifest fields and noncanonical entry ordering.

Logical artifact names use ASCII in this first schema. Physical input paths and source contents still support UTF-8. This restriction follows a reproduced macOS filesystem mismatch: composed `é/A.lean` and decomposed `e\u0301/B.lean` shared one materialized directory, allowing assembly followed by verification failure. Both forms now reject before output creation. General Unicode logical names need a portable encoding or normalization contract in a later schema. This remains an explicit portability gap within the full feature goal. Circuit and plan logical names must still match compiler metadata, so Unicode-generated artifact names also remain unsupported by this first bundler.

There are no timestamps or absolute build paths in the generated manifest. Identical selected bytes and compiler revision produce identical bundles regardless of recipe selection order. This does not establish determinism for the external compiler or key generator. Proof bytes and runtime values are excluded.

Limits are 64 entries, 256 MiB per payload, 1 GiB total payloads and 2 MiB per JSON artifact. The optional witness binding and control roles have smaller read limits of 512 KiB and 1 MiB. The optional Rust module has a 1 MiB read limit. Assembly and verification check these role limits before parsing their payloads. They retain bounded payload bytes in memory. These are interface limits, not a hostile filesystem or compiler sandbox. Filesystem inputs must stay under the caller's control during reading. Arbitrary source code or mislabeled binary data still requires a trusted producer.

Known private filenames, including `runtime-config.json`, witness JSON, preimages and private-state snapshots, reject even when selected under a public logical name. Physical input extensions must also match their selected role, such as `.lean`, `.zkir`, `.rs`, `.params`, `.prover` or `.verifier`. Extra bundle files reject. These checks prevent accidental inclusion of known execution files. They do not detect a secret embedded in a source constant, header, renamed binary or permitted program expression. The producer must select public programs and parameters. The tool does not resolve the Lean import closure or validate a build against its declared compiler revision.

## Rust consumer boundary

`artifacts::verify(root, trusted_digest)` returns `VerifiedBundle`. `manifest()` exposes immutable metadata. `file(Role::Plan)` and the other role getters return retained verified bytes. Source getters require an explicit logical source name. Consumers should execute these retained bytes instead of reopening mutable filesystem paths after verification.

The native assembler now accepts `noctium-assemble --bundle DIRECTORY --manifest-sha256 TRUSTED_DIGEST --config PRIVATE_CONFIG.json --ttl-unix UNIX_SECONDS NEW_OUTPUT_DIRECTORY`. This route verifies public inputs before reading private configuration, then passes retained bytes to `assembly::assemble_verified`. Rust callers use `artifacts::verify(root, Some(trusted_digest))` followed by the same consumer API. See [native assembler evidence](native-assembler.md) for the real-key checks, altered-plan/key/profile rejection and execution after deleting the verified bundle directory.

Low-level explicit-input assembly and the C ABI retain their documented trusted-artifact boundary. Hashes and matching schemas do not prove circuit/plan semantic equivalence, correct key generation, executable provenance, or correspondence with a deployed verifier key. The external source revisions and native-tool hashes are recorded declarations, not build attestations. Native parameter/key decoding and official checker/prover/ledger acceptance remain separate gates.

## Reproduced private-claim bundle

On 2026-11-16, the compiler source was exported from immutable revision `0851aca03586164708981742e9e833c080897661` into an isolated directory and built with Lean 4.35.0. Fresh compilation of `examples/PrivateClaim.lean` produced circuit and plan objects equal to the accepted native private-claim artifacts. The bundle used those fresh compiler outputs, the matching source/header/profile, public ledger parameters, accepted prover/verifier keys and original native build provenance. No witness, runtime configuration, proof preimage or private-state file was selected.

The output at `/private/tmp/noctium-public-bundle-0851aca` contains 10 payloads totaling 471,777 bytes, plus a 2,153-byte manifest. Its manifest SHA-256 is `17265934c3891263c3d7acb62abbb21777add0bf4131f28e3e909a1b3cb1d583`. A fresh native process with `env -i PATH=/usr/bin:/bin` verified the bundle against this external digest. No Node process participated. This packages previously accepted keys and parameters. It does not constitute a new deployment or proof run.

Eleven focused Rust tests cover canonical/reordered assembly, retained bytes after file mutation, every payload role's tampering rejection, target/source pin and plan mismatches, known private files and unknown plan fields, traversal/path conflicts/shared directory casing/symlinks, Unicode logical-name rejection with UTF-8 source preservation, missing/extra files, unsupported schemas and external-digest authentication. Synthetic key fixtures test integrity behavior only. The real bundle above exercises the accepted claim materials.
