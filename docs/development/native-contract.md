# Source-driven native contract workflow

Noctium's compiler is Lean. The [native Rust runtime](native-rust-runtime.md) executes its emitted plan and the [Rust assembler](native-assembler.md) constructs real native intents from retained authenticated bundle bytes. Neither execution nor assembly requires Node. The [C ABI](native-runtime-abi.md) exposes witness acquisition and private-state journals.

The commands below reproduce the earlier JavaScript development harness. They use native ledger/proving formats, but their orchestration and one assembler are JavaScript. This is an optional development workflow. New native applications should start with the [Rust client](native-client.md), which integrates [proof construction](native-proof-api.md), funding, signing, submission, finalized receipt validation and durable recovery. The [full host-neutral transaction ABI](https://github.com/awjreynolds/noctium/issues/61) remains separate work. Native key generation uses the pinned independent ZKIR CLI.

The helpers consume generated plans and ZKIR. They do not parse Lean source or invoke another source-language compiler. Use the linked Rust assembler workflow when embedding execution and assembly in a native application.

## Prepare the tools and chain

Install the pinned Lean toolchain, Rust 1.100.0, Node.js, Git, and a native C build toolchain. The isolated chain requires the pinned cached Docker images and verified public parameters described in [the localnet guide](../../scripts/localnet/README.md).

```sh
lake build
npm ci --prefix scripts/zkir --ignore-scripts
npm ci --prefix scripts/preview --ignore-scripts
node scripts/zkir/bootstrap-native.mjs /private/tmp/noctium-native-zkir
node scripts/localnet/stack.mjs up
mkdir -p build/native-claim
node scripts/localnet/ledger-parameters.mjs build/native-claim/ledger.params
```

The bootstrap builds the official independent ZKIR 3.2.0 CLI from pinned source with its lockfile. `ledger-parameters.mjs` checks the development genesis and reads real parameters from the isolated node. The runtime uses `parameters.transactionCostModel.runtimeCostModel` and the official `partitionTranscripts` API, rather than treating query cost as an execution budget.

## Compile the actual Lean source

```sh
.lake/build/bin/noctium compile examples/PrivateClaim.lean --output build/native-claim/source
/private/tmp/noctium-native-zkir/bin/zkir compile build/native-claim/source/PrivateClaim.claim.zkir build/native-claim/claim.prover build/native-claim/claim.verifier
node scripts/zkir/claim-config.mjs build/native-claim/inputs.json
node scripts/zkir/native-contract.mjs build/native-claim/source/PrivateClaim.claim.impact.json build/native-claim/source/PrivateClaim.claim.zkir build/native-claim/claim.prover build/native-claim/claim.verifier build/native-claim/artifacts --ledger-params build/native-claim/ledger.params --config build/native-claim/inputs.json --prove
node scripts/localnet/deploy-native.mjs build/native-claim/artifacts build/native-claim/local
```

The config generator uses publicly known development values: secret 42, campaign 9, siblings 17 and 23, and directions false and true. It computes the public root and nullifier through the official Native-field Poseidon implementation. It also defines the five invalid cases for the harness. The compiler source defines the hash domains and relation. The config file supplies example data only.

`--prove` is optional. It creates a diagnostic standalone proof with binding input 42. The funded transaction runner creates its own correctly bound proof and does not reuse that diagnostic proof. Proving requests contain witnesses, so the optional proof-server override accepts HTTP or HTTPS on loopback only and refuses credentials and redirects.

If SDK dependencies are installed outside `scripts/preview`, set `NOCTIUM_WALLET_DEPENDENCIES` to their package directory before running `deploy-native.mjs`. The qualified setup used `/private/tmp/noctium-preview-wallet`.

## Emitted artifacts and validation

The assembler reads schema version 1 from `PrivateClaim.claim.impact.json`. This file contains the actual source contract's state schema, circuit input/output schema, expression trees, state guards, VM operations, and ordered reads. No placeholder root or nullifier replacement occurs.

The runtime materializes supported cell reads and empty initial maps, computes declared outputs, builds the exact VM transcript, and registers the native verifier key in a `ContractOperation`. It constructs `ContractState`, `ContractDeploy`, `ContractCallPrototype`, and serialized intents using the official ledger API. It rejects unsupported schemas, unsafe entrypoint artifact names, unknown options, duplicate options, unknown inputs, and noncanonical field values.

The output directory contains `source-plan.json`, `runtime-config.json`, `ledger.params`, native keys and circuits, serialized initial/predicted state, deployment/call intents, and `native-contract.json`. Witness-bearing files use mode 0600. Keep the directory private. Each assembly invocation randomizes the deployment address, so keys, address, state, and intents must stay together.

The transaction runner refuses the wrong genesis, funds through the published local development identity, requires finalized matching receipts, checks accepted state against predicted state, and verifies invalid witnesses and replay rejection. Its accepted evidence is `local/native-localnet.json`.

Funding and contract-state queries use two RPC fetch workers, two fetch-compute workers and two wallet replay workers. Each toolkit command has a ten-minute timeout. These explicit flags override the pinned toolkit's 20-worker fetch default, which exhausted the development node's 3 GiB memory limit during a historical scan. The runner keeps fetch data and wallet snapshots in a private `.native-toolkit-*` directory inside the work directory. Sequential commands share these disk caches. Each invocation, including `--resume-call`, starts with fresh caches, so a reset development chain or abandoned run does not supply old snapshots. Completed cache directories are disposable development data.

Check the bounded configuration without a running chain:

```sh
node --test tests/localnet-toolkit-config.mjs
```

The 2026-11-16 check also exercised the pinned toolkit with network-disabled funding/state dry runs, including an inherited 20-thread replay setting. The explicit two-thread flag prevailed. Two live read-only state queries then used this configuration on the isolated chain. The first fetched 1,083 blocks with two fetch and two compute workers. The second fetched two new blocks and read 1,082 from the shared disk cache. Both returned the accepted state bytes with SHA-256 `d03deaed2a47e077412acd4db0fb3069e47cd41d05472eebb3c8182f0c938dc3`. The node stayed running at 256.5 MiB after the checks. No new deployment or claim was submitted for this configuration check.

The standalone checks are also reusable:

```sh
node scripts/zkir/check-native-cases.mjs build/native-claim/artifacts build/native-claim/artifacts/initial-state.bin negative
node scripts/zkir/check-native-cases.mjs build/native-claim/artifacts build/native-claim/local/observed-state.bin replay
```

The current helper supports the initial source subset: Native-field and Boolean inputs, field arithmetic, equality, eager selection, Poseidon, state-cell reads, and empty initial maps with member checks and insertion. Unsupported source features must fail before a support claim. The accepted source-to-ledger evidence is [native-localnet.md](native-localnet.md).

## Compare the block time

`blockTimeBefore(deadline) as before` and `blockTimeAfter(deadline) as after`
compare the ledger block time against a `UInt 64` deadline in Unix seconds.
Both are false at equality. A guarded inactive comparison supplies false
without reading the clock. A private deadline or activity condition needs
an explicit disclosure because the native transcript exposes the comparison
operands and activity. [Midnight kernel reference](https://docs.midnight.network/compact/reference/ledger-adt#blocktimelessthan)

The compiler emits native Impact operations to fetch the block time and
bind the Boolean result to the ZKIR statement. The native VM re-evaluates
the comparison against its execution context. If the clock crosses the
deadline and changes a bound result, the transcript fails. The caller
must prepare a new proof for the changed result.

Use `PreparedProof::from_config_in_block` with a prospective ledger
`BlockContext` in the Rust SDK. The native localnet client takes this
context from its checked node snapshot. The low-level
`prepare_with_context` also accepts an explicit query context.
An active comparison fails preparation when no clock is supplied.
The [source fixture](../../tests/NativeBlockTime.lean),
[Compact oracle](../../tests/compact/block-time.mjs) and
[native checker fixture](../../runtime/tests/native_block_time.rs)
check the strict boundaries. A hosted SDK path that does not provide a
block context still requires integration.

On Ledger 9.1.0.1 localnet, the Rust SDK finalized deployment at block 67
and a call using both strict predicates at block 70. The exact observed
contract state matched the SDK prediction at both blocks. Native sizing
reported K8 and 126 rows. The deadline-crossing rejection was checked in
native VM replay. [Localnet receipt](native-block-time-localnet-receipt.json)
