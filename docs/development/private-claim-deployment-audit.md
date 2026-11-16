# Noctium PrivateClaim deployment audit

This audit joins the selected PrivateClaim source certificate to native key generation and a particular finalized deployment. Its guarantee is `PrivateClaimDeploymentIdentity/v1`, for the selected ZKIR 3.2.1 profile and the existing `successfulClaimPublicTranscriptV1` observer. The result is a qualified identity statement under the recorded native, toolchain, SRS and trusted-node assumptions.

The controller starts by running the closed [exact-byte artifact audit](private-claim-artifact-certificates.md), using an independently supplied authority digest. It then generates and checks native keys, constructs an authenticated public bundle and checks the actual deployed operation and initialized state. A public auditor needs public artifacts and a trusted node endpoint. Witnesses, wallet seeds and private journals are excluded from the public verification interface.

The source authority used by the retained qualification is commit `925164d0e17d994038d77d3b2b71c410619557d3`, tree `380ced01c6ced4409c7aedf59a9985d21b50f582`, authority SHA-256 `5911db364d99b11fdaab6af215264fc59e8c8f8f86d13d2981eb7c246d2ca9eb`. Current Noctium branding and SDK revisions do not replace this historical compiler/proof identity. Existing `Nightlean.*` proof names and wire-format identifiers remain stable compatibility identifiers.

## The checked join

The externally pinned source audit retains the source commit/tree and closure, compiler product, imported products, trusted model, theorem closure, selected profile and exact artifact bytes. It replays the selected source and native proof obligations through the kernel. The deployment controller retains the trusted authority's source, compiler and imported products, model, certificate and artifacts under their independently pinned hashes. It executes the unchanged checker from that private snapshot. Candidate code and initializers are never executed by the source checker.

Key generation consumes exactly `PrivateClaim.claim.zkir`, the audited 55-instruction CALL relation. The 27-instruction `claimRelation.zkir` is the standalone relation and is excluded as the deployed key-generation input. The selected native CLI runs `zkir compile` against a retained copy of those CALL bytes and the exact pinned SRS. The invocation record binds the input, SRS, native source revision, executable, Cargo lockfile, Rust version, command and output keys.

The selected Rust implementation independently calls `IrSource::keygen` with the same retained CALL bytes and checked SRS. Both serialized outputs must equal the CLI-produced proving and verifier keys. A manifest listing independent circuit and key hashes does not satisfy this step. Public verification re-executes CLI key generation and Rust regeneration, compares the actual key bytes and then verifies the observed call proof against the regenerated expected verifier key.

The native tool pin is `midnight-zkir` source revision `7a51b3385bbf4bce3604df87a7c70867c9ab43c0`, Rust 1.100.0. The upstream native CLI still reports version `3.2.0`; the requested release, source revision, executable and lockfile identify the selected 3.2.1 build. The native ledger dependency keeps its existing exact git pin. The native CLI provenance describes the actual CLI invocation. Rust helper execution has a separate externally supplied executable digest.

`artifacts::assemble` and `verify` retain the selected public payload bytes. The join requires the bundle's compiler revision to equal the external authority source commit, and compares its source, plan, CALL, profile and metadata with the audited identities. `PreparedProof` freezes the call, checks the real local proof with the retained verifier key and attaches the native ledger proof. SDK 60 funds, approves, seals, submits, observes finality and reconciles its private journal through the existing host interfaces.

## Initialization and revision

The public specification independently selects `acceptedRoot`, `campaignId` and an explicitly empty `spent` map. Private invocation configuration does not define the expected deployment. Before execution, the helper compares its constructed state with the complete expected native `ContractState`:

- The expected public root and campaign, with the native charged-state encoding and an empty map.
- Exactly one `claim` operation with the regenerated key in `ContractOperation.v3`, no legacy `v2` key and no stored IR.
- Empty balances and maintenance authority with an empty committee, threshold 1 and counter 0.

The native constructor derives the address from the full deployment state and nonce. Public verification requires the independently supplied expected address and deployment-record digest, derives native transaction and intent hashes from the sealed public bytes and checks the exact action, address and entrypoint.

At the finalized deployment block, the complete observed initial state must match. The later valid claim must be accepted with the exact expected native state and a proof which verifies under the regenerated key. Receipt checking links numbered parent hashes through the captured finalized head and checks the exact extrinsic, event phase/index, native transaction ID, contract event, address and full state.

A final read checks the current operation map and maintenance authority against the original revision. A different key, entrypoint, stored IR or maintenance revision invalidates the old qualification. Restoring an earlier key after a maintenance counter change also invalidates it. Mutable claim data such as the spent map is observed at the recorded call block and is excluded from the current code-revision comparison.

The retained negative tests use real public native keys and states. They exercise changed-key and maintenance-counter snapshots. The fixture starts with no maintenance committee, so this qualification does not authorize or perform a live upgrade.

## Parameter snapshots and live quotes

Cryptographic key generation uses the SRS, separately from native `LedgerParameters`. The specification pins the complete canonical parameter bytes and a finalized block hash/height. The verifier reads those exact bytes at that historical reference and links that block to the captured finalized head.

Native `apply_post_block_update` changes `LedgerParameters.fee_prices` as block fullness changes. The guarantee explicitly selects `adaptive-fee-prices-v1`. Later execution and auditing permit only this native typed field to vary. Every other parameter must match through canonical serialization of the native structure. The implementation replaces the expected structure's `fee_prices` with the actual typed field and compares the complete encoded structures. It does not mask byte offsets or relabel a normalized hash as a full parameter hash.

Each SDK funding step records the full actual parameter bytes, SHA-256 and finalized reference from the precise snapshot supplied to funding and sealing. Public auditing authenticates every recorded quote against its historical block. Mutating prices in the originally pinned snapshot still rejects. Genuine later protocol price updates pass with their own full quote hashes. Changes to cost models, limits, DUST parameters, TTLs, adjustment policy or any other field reject this revision.

The read-only native runtime API is `MidnightRuntimeApi_get_ledger_parameters`, decoded as the checked Result/Vec envelope followed by the complete native tagged parameters. The adapter validates the pinned runtime and metadata and the reference's finalized ancestry before accepting the bytes. Runtime upgrades fail closed.

## Reproduction interfaces

Build the Rust helper from the intended reviewed SDK source:

```sh
cargo +1.100.0 build --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321,localnet \
  --example audit_claim_deployment
```

Measure and independently pin its executable SHA-256. The Python controller requires `--rust-helper` and `--rust-helper-sha256` on every command. It reads each bounded regular input once, hashes and parses the same retained JSON bytes, and executes only retained CLI/helper bytes checked against the original independent pins. Executable and invocation snapshots are temporary and private. Run Python without optimization, since optimized execution is rejected.

The public input set consists of the independently pinned issue 56 authority and audited candidate, the public deployment specification and digest, the qualified native CLI build manifest/executable, and exact native SRS bytes. The specification records:

```text
schemaVersion: 1
guaranteeVersion: PrivateClaimDeploymentIdentity/v1
authoritySha256, sourceCommit, sourceTree
entrypoint: claim
initialization: acceptedRoot, campaignId, spent: []
policy: ledger network ID, genesis, runtime spec/transaction versions,
        selected contract profile and DUST budget
ledgerParametersSha256, ledgerParametersBlockHash, ledgerParametersHeight
ledgerPricePolicy: adaptive-fee-prices-v1
srsSha256, nativeToolchainSha256
runtimeCodeHash, metadataSha256
```

The helper's `measure-parameters` request performs a public native snapshot read and writes canonical parameter bytes plus their finalized reference. Its result is explicitly a measurement. The operator supplies the independent specification pin; a candidate's own digest is insufficient authority.

The controller is `scripts/proofs/check-private-claim-deployment.py`. Every command requires these public arguments:

```text
--authority AUTHORITY.json --authority-sha256 TRUSTED_AUTHORITY_SHA
--audit-bundle AUDITED_56_DIRECTORY
--specification SPECIFICATION.json --specification-sha256 TRUSTED_SPEC_SHA
--native-toolchain BUILD_MANIFEST.json --native-cli NATIVE_ZKIR
--srs PINNED_SRS --rust-helper RUST_HELPER
--rust-helper-sha256 TRUSTED_HELPER_SHA --output NEW_DIRECTORY
```

`build` additionally takes `--ledger-parameters PINNED_NATIVE_PARAMETERS`. It consumes no private invocation configuration. Its output contains the native public bundle, exact source-audit result, CLI invocation record, independent Rust comparison and a completion manifest.

`execute` additionally takes `--deployment-bundle PUBLIC_BUILD`, `--endpoint LOOPBACK_RPC`, `--private-config PRIVATE_INVOCATION`, `--private-journal PRIVATE_DIRECTORY` and `--parameter-cache EXPLICIT_CACHE`. The retained development execution requires both `--approve` and `--public-development-genesis`. That fixture is restricted to the qualified isolated development genesis. The Rust application performs proof, funding, sealing, submission and journal reconciliation in-process. Preparatory source auditing and key-generation tools run outside that application path. See [native-client.md](native-client.md) for SDK 60's host and cancellation contract.

Private invocation request files are temporary and private. Public outputs contain no witness, seed or private journal. Keep the host journal outside the public output directory. The example's Boolean host write is an SDK integration fixture, separate from source-program private-effect assurance.

`verify` additionally takes `--deployment-bundle PUBLIC_BUILD`, `--endpoint TRUSTED_LOOPBACK_RPC`, `--record PUBLIC_DEPLOYMENT.json`, `--record-sha256 TRUSTED_RECORD_SHA` and `--expected-address EXPECTED_ADDRESS`. It accepts no private configuration, seed or journal argument. The record pin and address must come from the intended deployment reference, independently of candidate claims. A public audit replays the source audit, both key-generation paths, historical/full-state checks, actual call-proof verification and current operation-revision check.

The selected adapter deliberately targets an explicit loopback development node. A production host requires its own qualified endpoint/finality policy and wallet adapter. The controller does not deploy to production.

## Published public fixture

[tests/deployment57-public/manifest.json](../../tests/deployment57-public/manifest.json) inventories seven public files, totaling 1,327,014 bytes. They retain the exact specification, sealed transaction/deployment record, original source authority, original native tool manifest, historical parameter bytes and the parent's separate public audit. The manifest lists each payload's size and SHA-256. Its digest is recorded separately in the evidence receipt. Downloaded manifests do not supply their own trust authority.

These files contain public transaction/proof/state bytes and build identities. They exclude private invocation configuration, witnesses, wallet seeds, private journals, executable snapshots, generated key copies, SRS files and caches. The original authority and native manifests preserve their historical paths and bytes. Those paths describe the qualified host. They do not refer to files distributed in this fixture.

The source authority includes its reviewed public trust input. Recover those exact bytes and check the independently published pins before preparing a fresh authority:

```sh
PUBLIC=/absolute/path/to/noctium/tests/deployment57-public
WORK=$(mktemp -d)
python3 - "$PUBLIC" "$WORK" <<'PY'
import hashlib, json, pathlib, sys
public, work = map(pathlib.Path, sys.argv[1:])
data = (public / "source-authority.json").read_bytes()
assert hashlib.sha256(data).hexdigest() == "5911db364d99b11fdaab6af215264fc59e8c8f8f86d13d2981eb7c246d2ca9eb"
authority = json.loads(data)
trust = (json.dumps(authority["trustInput"], sort_keys=True,
                   separators=(",", ":"), ensure_ascii=True) + "\n").encode()
assert hashlib.sha256(trust).hexdigest() == "5d7e11b0948e6e1f86de23b3d4d13a112a66d43cc4df6f76fe6edf7334684e4b"
(work / "reviewed-trust-input.json").write_bytes(trust)
PY
git worktree add --detach "$WORK/source" 925164d0e17d994038d77d3b2b71c410619557d3
python3 "$WORK/source/scripts/proofs/check-private-claim-artifacts.py" prepare-authority \
  --trust-input "$WORK/reviewed-trust-input.json" \
  --trust-input-sha256 5d7e11b0948e6e1f86de23b3d4d13a112a66d43cc4df6f76fe6edf7334684e4b \
  --output-dir "$WORK/authority"
shasum -a 256 "$WORK/authority/authority.json"
python3 "$WORK/source/scripts/proofs/check-private-claim-artifacts.py" build-candidate \
  --authority "$WORK/authority/authority.json" \
  --authority-sha256 5911db364d99b11fdaab6af215264fc59e8c8f8f86d13d2981eb7c246d2ca9eb \
  --bundle "$WORK/candidate"
```

The reconstructed authority must match `5911db364d99b11fdaab6af215264fc59e8c8f8f86d13d2981eb7c246d2ca9eb`. The retained Lean 4.35.0 closure and native CLI build target Darwin ARM64. Exact product reproduction requires that pinned compatible toolchain environment, including the authority's measured toolchain root. A different toolchain requires a separately reviewed authority rather than editing this historical record.

Build the auditor helper from its separate SDK revision, then measure and approve that local executable through the auditor's host policy:

```sh
git worktree add --detach "$WORK/sdk" c48fc4b7aa1a06926c15fb83026fb51ce80c203c
CARGO_TARGET_DIR="$WORK/rust-target" cargo +1.100.0 build \
  --manifest-path "$WORK/sdk/runtime/Cargo.toml" --locked \
  --no-default-features --features zkir-321,localnet \
  --example audit_claim_deployment
HELPER="$WORK/rust-target/debug/examples/audit_claim_deployment"
shasum -a 256 "$HELPER"
```

The original helper digest `b10d0d3070d03c19c76c548f65382795fc490e1f8e84db3dbcaa026ac54ce6d3` identifies the qualified retained host binary. Another host builds, measures and independently approves its own helper from the same reviewed source. That local digest becomes `APPROVED_HELPER_SHA` below. This does not claim universal executable-byte reproducibility. The native CLI remains subject to its original, stricter executable/source/lockfile pin in `native-toolchain.json`. Obtain its exact qualified build and the public `bls_midnight_2p9` SRS, SHA-256 `b9009f1098bcefffec3c461ab3a5e3a17f7e5599f0f08c70fcdc55a89227bcbd`, from the qualified provider. Neither executable nor SRS is redistributed here.

Set `NATIVE_CLI`, `SRS` and `APPROVED_HELPER_SHA` to those independently checked local inputs. Reconstruct public material without private invocation inputs:

```sh
controller() {
  audit_mode="$1"
  shift
  python3 "$WORK/sdk/scripts/proofs/check-private-claim-deployment.py" "$audit_mode" \
    --authority "$WORK/authority/authority.json" \
    --authority-sha256 5911db364d99b11fdaab6af215264fc59e8c8f8f86d13d2981eb7c246d2ca9eb \
    --audit-bundle "$WORK/candidate" \
    --specification "$PUBLIC/specification.json" \
    --specification-sha256 17cae31f6a73eec24a729a6ef74187ccf11264a96c8bc1355f18672f94db1d1e \
    --native-toolchain "$PUBLIC/native-toolchain.json" --native-cli "$NATIVE_CLI" \
    --srs "$SRS" --rust-helper "$HELPER" --rust-helper-sha256 "$APPROVED_HELPER_SHA" \
    "$@"
}
controller build --output "$WORK/public-material" --ledger-parameters "$PUBLIC/ledger.params"
```

Both regenerated serialized keys and the native bundle manifest must match `manifest.json`'s `publicMaterialReconstruction` hashes. The outer public manifest records the producer helper digest, so another approved helper digest changes that outer manifest. Exact repetition on the original qualified helper also reproduces the original outer manifest.

Full public verification needs a trusted loopback endpoint retaining the recorded development genesis and finalized history. A newly started chain does not supply those historical receipts. Set `RPC_ENDPOINT` to that qualified endpoint:

```sh
controller verify --output "$WORK/public-audit" \
  --deployment-bundle "$WORK/public-material" --endpoint "$RPC_ENDPOINT" \
  --record "$PUBLIC/deployment.json" \
  --record-sha256 803bd8ce488ef79be65b7b3f466d4827b4441070ea9074cd24c0afdde6eb819c \
  --expected-address d1a8d4c7866ef9f670232ae4f084a42e7555d7c98677b373550ba3c5e69c7092
```

The retained `audit.json` records the parent's completed replay against that history. Public source/key reconstruction requires no node or private input. Historical receipts, quotes, state and current revision require the trusted-node reads described above. The fixture is a reproducible public audit input set and development deployment reference, with no consensus light-client proof.

## Evidence and assumptions

[tests/private-claim-deployment-evidence.json](../../tests/private-claim-deployment-evidence.json) records the source authority, guarantee/specification version, native and SRS identities, actual public deployment reference, observed initial V3 key/state, valid call, full quotes, public-only verification and negative results. Random deployment nonces and chain timing produce a new address/reference on a fresh run. The source and key-generation checks remain reproducible from the pinned public inputs.

The implementation qualification uses published commit `c48fc4b7aa1a06926c15fb83026fb51ce80c203c`, tree `2f8a7feea3382eeb6ec74d8a7ce9d1faaf373ee3`. A fresh Git archive matched all 308 tracked blobs and file modes, then built the separately pinned Rust helper. That snapshot passed public bundle construction, funded native deployment and claim, a separate public-only verification, 15 material/revision negatives and seven file-replacement guards. Ordinary suites passed 111 tests for 3.2.0 and 115 for 3.2.1. The selected deployment and claim finalized at blocks 5764 and 5767. The evidence retains their complete public references and per-funding parameter quotes. This SDK implementation revision is separate from the source authority `925164d` above.

The guarantee assumes qualified native key generation, the selected parser/VM/prover/verifier implementations and their cryptographic assumptions. SRS ceremony provenance and pairing relations remain externally trusted. The host supplies trusted toolchain and durable-store capabilities. Finality, canonical history, parameter/state reads and runtime-code identity rely on the selected trusted node; this adapter supplies no consensus light-client proof.

The source certificate preserves its reviewed model/policy and axiom closure. The operator's root/campaign selection does not acquire unconditional business-specification review. Proof-byte zero knowledge, bootstrap verification and universal compiler preservation remain separate claims. Original source-audit and assembler status fields retain their original layer scopes; the joined result reports the selected deployment identity qualification.
