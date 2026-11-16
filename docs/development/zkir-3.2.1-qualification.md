# Native ZKIR 3.2.1 qualification

Checked on 2026-11-16. This document preserves the earlier experimental native-toolchain qualification, separate from the existing [default profile](../../profiles/midnight-ledger-9.json) and its [3.2.0 localnet evidence](native-localnet.md). The [experimental manifest](../../profiles/midnight-ledger-9-zkir-3.2.1.json) records the source pin and limited qualification scope. At the time of this experiment, the Lean target selector accepted the existing default target. The later [selectable-profile integration](zkir-3.2.1-integrated.md) records a separate exact-commit build and qualification. No Compact compiler or runtime was installed or invoked for these checks.

## Upstream identity

The official annotated `zkir-3.2.1` tag resolves through tag object `03c05b976942a7a36ae48bb442d1c828776d0558` to source commit `7a51b3385bbf4bce3604df87a7c70867c9ab43c0`. This is also the native ZKIR pin in the Compact 0.36.1 reference lockfile. Compact is reference material only. [Official tag](https://github.com/midnightntwrk/midnight-zkir/releases/tag/zkir-3.2.1), [reference lockfile](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/flake.lock).

The tagged `zkir/Cargo.toml` still declares `version = "3.2.0"`. A clean native build therefore reports `midnight-zkir 3.2.0`. The release label, exact source commit and executable hash identify this build. The banner alone does not distinguish the two releases. Nightlean preserves the upstream source without editing its version. The packaged official WASM release reports package version 3.2.1. [Tagged Cargo manifest](https://github.com/midnightntwrk/midnight-zkir/blob/7a51b3385bbf4bce3604df87a7c70867c9ab43c0/zkir/Cargo.toml), [official release asset](https://github.com/midnightntwrk/midnight-zkir/releases/download/zkir-3.2.1/midnight-zkir-v3-3.2.1.tgz).

| Item | Observed value |
| --- | --- |
| Native build | Clean official source, Rust 1.100.0, Darwin arm64, locked dependencies |
| Native executable SHA-256 | `7396c9a368e70fb66cb91f39d1508c9f983cacc8d3bc27f7a94e12d9fe327c40` |
| Cargo.lock SHA-256 | `f6044eb43d4d8e6f2ed3dab33cb8f70fe1a59784fcc987e18aef4dab46a16c6b` |
| Official 3.2.1 WASM tarball SHA-256 | `f2f4d6c1aaa85e2d9cec1c9f204f4f47ae5c7650ef170a68b1675441ea037133` |
| Locked circuit/stdlib crates | midnight-circuits 7.3.0, midnight-zk-stdlib 2.4.0 |

Build the new version in a separate directory:

```sh
RUSTUP_HOME=/private/tmp/nightlean-rustup \
CARGO_HOME=/private/tmp/nightlean-cargo \
NIGHTLEAN_CARGO=/private/tmp/nightlean-cargo/bin/cargo \
CARGO_TARGET_DIR=/private/tmp/nightlean-zkir-321-build \
node scripts/zkir/bootstrap-native.mjs --version 3.2.1 /private/tmp/nightlean-native-zkir-321
```

The existing positional-directory invocation still selects 3.2.0. `--version` accepts only the two known source pins. Omitting the directory selects a separate default directory for each version. `NIGHTLEAN_ZKIR_SOURCE` still requires the exact selected revision and clean tracked source. The manifest records requested release, actual CLI version, source revision, binary hash and lockfile hash. A compatibility run rebuilt 3.2.0 into `/private/tmp/nightlean-bootstrap-compat-320` and retained executable SHA-256 `2664d4d6f97c04e882b4208b9926f27f1e1d03082ca508e69f0145c491aa694a`. The existing `/private/tmp/nightlean-native-zkir` executable retained the same hash.

## Patch regressions

The 3.2.1 release fixes chip selection when curve types arise inside a circuit. The previous scan missed types introduced through operations such as `JubjubScalarFromNative`, `EcMulGenerator` and `LoadConstant`. The new type-inference pass tracks every intermediate and enables its chip. The release changes no IR language syntax and preserves previously working keys. [Release description](https://github.com/midnightntwrk/midnight-zkir/releases/tag/zkir-3.2.1), [type-inference implementation](https://github.com/midnightntwrk/midnight-zkir/blob/7a51b3385bbf4bce3604df87a7c70867c9ab43c0/zkir/src/type_inference.rs), [chip selection](https://github.com/midnightntwrk/midnight-zkir/blob/7a51b3385bbf4bce3604df87a7c70867c9ab43c0/zkir/src/ir_vm.rs#L1629).

[jubjub-intermediate.zkir](../../tests/zkir321/jubjub-intermediate.zkir) takes a Native scalar and produces an intermediate Jubjub scalar and generator multiple. Its input signature contains no Jubjub type. Independent native 3.2.0 keygen exits 101 with `ZkStdLibArch must enable jubjub`. The clean tagged 3.2.1 executable succeeds at k=10, 684 rows. This reproduces the actual upstream key-generation failure. The official 3.2.1 checker accepts input 7. Its WASM prover generated a 4,085-byte standalone proof with SHA-256 `056026cf178102002ee91f5d71219f4309727b443e14461306a5973fb0751733`. This Jubjub relation was not deployed or accepted by the ledger. Nightlean's frontend has no Jubjub source type, so this fixture establishes backend regression coverage only.

The Boolean deserialization correction belongs to Compact 0.36.1 lowering, separate from the ZKIR patch. The downcast unsigned range changes from 8 to 255. The reference regression short-circuits `flag || deserialize<Boolean,1>(output)`. Treating 8 as a maximum value instead of an eight-bit range excluded valid bytes before the Boolean validity check. [Exact reference patch](https://github.com/LFDT-Minokawa/compact/compare/compactc-v0.36.0...compactc-v0.36.1), [corrected lowering](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/analysis-passes/expand-serialize.ss).

[boolean-deserialization-contract.zkir](../../tests/zkir321/boolean-deserialization-contract.zkir) is an independently specified raw-ZKIR semantic contract. Byte inputs are constrained to eight bits. An inactive deserialization selects zero before Boolean validity checking. The active case accepts only zero or one. A separate expected-result input prevents a wrong decoded result from passing. The official 3.2.1 checker accepts false, true, guarded byte 2 and guarded byte 255. The checker rejects unguarded 2/255, byte 256, guard 2, and two wrong-result cases. Native keygen succeeds at k=9, 20 rows. This fixture does not use Compact-generated output and does not claim Nightlean supports byte deserialization or guarded source execution. Both source capabilities remain unimplemented.

Run the checker fixtures after downloading and verifying the official release asset:

```sh
node tests/zkir321/check-fixtures.mjs /private/tmp/nightlean-zkir321-wasm/package/midnight_zkir_wasm_fs.js
```

## Existing Native/Bool claim

The existing actual Lean source circuit and symbolic ledger plan were reused without editing the compiler target. Fresh tagged 3.2.1 native keygen produced k=9 keys. The official 3.2.1 WASM checker accepted the resulting ledger proof preimage with 21 transcript activity entries. The existing isolated proof server 9.0.0 produced a 3,852-byte proof using these keys. The bridge package lock remains on its previous 3.2.0 checker, and the separate release checker independently checks the new run.

| Artifact | SHA-256 |
| --- | --- |
| Native claim ZKIR | `c569dd887fdf6aa3bdd2c8e2358985657ad3612eb72e0eb16f28682bb2b2b81c` |
| Prover key | `b9b7e5dd38f01468aecf6b698a74905800227a41e3ca7d7ef302dc287fc64e55` |
| Verifier key | `bc1e417d74922fee9a97778a0a00e7f9910e38f356cba94aa2dee0788b3fa536` |
| Standalone native claim proof from this run | `7efdd33a494fc326cc55bf886a652e3b3bb1c9961f4c9482e9084aa6f86c46a8` |

Both new key hashes equal the existing working 3.2.0 claim keys. This confirms the release's backward-compatible-key statement for this selected circuit. Different randomness produces different proof bytes.

Run the independent new checker against assembled artifacts:

```sh
node tests/zkir321/check-native-claim.mjs \
  /private/tmp/nightlean-zkir321-wasm/package/midnight_zkir_wasm_fs.js \
  /private/tmp/nightlean-zkir321-qualification/artifacts
```

The local ledger run uses the existing isolated Nightlean development node on port 19944 and proof server on port 16300. Its genesis is `0x823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d`, runtime spec 2001100, transaction version 4. The published development wallet funds the run. No authzk service or wallet is changed.

The node finalized a fresh deployment and claim for contract `39a612eb9b2ec023913e75d4644eebcc6f3f8eb7730de1df55d76d30bf7645f2`. Both receipts contain `TxApplied` and the expected contract event. [Machine evidence](../../tests/zkir321/qualification-evidence.json) retains the exact finalized blocks, transaction identities, tool pins and regression outcomes.

| Receipt | Finalized height | Ledger transaction hash |
| --- | --- | --- |
| ContractDeploy | 1012 | `0x74df72c829f516c5a28ae14c32082903a70e6f9c2b9e341ed84476af2de2102d` |
| ContractCall | 1015 | `0x19d5b126044cbc0bd8ce98d05a4f744e3775e8c96835b367984449c0f4281069` |

The fetched post-claim state exactly matches predicted bytes, SHA-256 `d03deaed2a47e077412acd4db0fb3069e47cd41d05472eebb3c8182f0c938dc3`. Five changes to the secret, Merkle path, direction, root and nullifier failed the official checker before submission. Replay failed the host's absent-key guard against the fetched spent state. No replay transaction was submitted. A second state fetch confirmed unchanged ledger bytes.

The first funding attempt used the existing helper's default 20 RPC fetch workers to replay 981 historical blocks. The isolated node hit its 3 GiB container memory limit, with Docker `OOMKilled=true` and exit 137 at `2026-11-16T15:33:04.187093465Z`. The existing node was restarted once with its chain state preserved. A temporary qualification harness reused the already generated deploy transaction, reduced fetch/compute/replay concurrency to two, and used a separate persistent qualification cache. That run produced the receipts above. This bounded harness changed no tracked deployment helper. The successful replay cache is `/private/tmp/nightlean-zkir321-qualification/localnet/qualification-fetch.db`. Future long-history runs should bound toolkit fetch concurrency rather than repeat the 20-worker in-memory scan.

## Qualification boundary

This experiment does not qualify a public network, the complete ZKIR instruction set, source Jubjub types, generic deserialization, foreign curves, signatures, token operations, events, cross-contract calls or full feature equivalence. Library presence supplies implementation options. Each source feature still needs its own type rules, lowering, runtime ABI and acceptance cases from the [feature baseline](../research/compact-equivalence-baseline.md).

This experiment left the default profile, Lean target parser, existing 3.2.0 receipts and native Rust probe on their original versions. The later selectable-profile integration is recorded separately, with matching source pins, consumer validation and new qualification evidence. Historical receipt and provenance files from this experiment remain unchanged.
