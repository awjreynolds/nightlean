# Source-driven native contract workflow

Nightlean's compiler is Lean. The runtime helpers consume its emitted symbolic plan and native ZKIR, supply witnesses, execute the native VM, assemble ledger contract artifacts, and call the official prover. They do not parse Lean source or invoke another source-language compiler.

## Prepare the tools and chain

Install the pinned Lean toolchain, Rust 1.100.0, Node.js, Git, and a native C build toolchain. The isolated chain requires the pinned cached Docker images and verified public parameters described in [the localnet guide](../../scripts/localnet/README.md).

```sh
lake build
npm ci --prefix scripts/zkir --ignore-scripts
npm ci --prefix scripts/preview --ignore-scripts
node scripts/zkir/bootstrap-native.mjs /private/tmp/nightlean-native-zkir
node scripts/localnet/stack.mjs up
mkdir -p build/native-claim
node scripts/localnet/ledger-parameters.mjs build/native-claim/ledger.params
```

The bootstrap builds the official independent ZKIR 3.2.0 CLI from pinned source with its lockfile. `ledger-parameters.mjs` checks the development genesis and reads real parameters from the isolated node. The runtime uses `parameters.transactionCostModel.runtimeCostModel` and the official `partitionTranscripts` API, rather than treating query cost as an execution budget.

## Compile the actual Lean source

```sh
.lake/build/bin/nightlean compile examples/PrivateClaim.lean --output build/native-claim/source
/private/tmp/nightlean-native-zkir/bin/zkir compile build/native-claim/source/PrivateClaim.claim.zkir build/native-claim/claim.prover build/native-claim/claim.verifier
node scripts/zkir/claim-config.mjs build/native-claim/inputs.json
node scripts/zkir/native-contract.mjs build/native-claim/source/PrivateClaim.claim.impact.json build/native-claim/source/PrivateClaim.claim.zkir build/native-claim/claim.prover build/native-claim/claim.verifier build/native-claim/artifacts --ledger-params build/native-claim/ledger.params --config build/native-claim/inputs.json --prove
node scripts/localnet/deploy-native.mjs build/native-claim/artifacts build/native-claim/local
```

The config generator uses publicly known development values: secret 42, campaign 9, siblings 17 and 23, and directions false and true. It computes the public root and nullifier through the official Native-field Poseidon implementation. It also defines the five invalid cases for the harness. The compiler source defines the hash domains and relation. The config file supplies example data only.

`--prove` is optional. It creates a diagnostic standalone proof with binding input 42. The funded transaction runner creates its own correctly bound proof and does not reuse that diagnostic proof. Proving requests contain witnesses, so the optional proof-server override accepts HTTP or HTTPS on loopback only and refuses credentials and redirects.

If SDK dependencies are installed outside `scripts/preview`, set `NIGHTLEAN_WALLET_DEPENDENCIES` to their package directory before running `deploy-native.mjs`. The qualified setup used `/private/tmp/nightlean-preview-wallet`.

## Emitted artifacts and validation

The assembler reads schema version 1 from `PrivateClaim.claim.impact.json`. This file contains the actual source contract's state schema, circuit input/output schema, expression trees, state guards, VM operations, and ordered reads. No placeholder root or nullifier replacement occurs.

The runtime materializes supported cell reads and empty initial maps, computes declared outputs, builds the exact VM transcript, and registers the native verifier key in a `ContractOperation`. It constructs `ContractState`, `ContractDeploy`, `ContractCallPrototype`, and serialized intents using the official ledger API. It rejects unsupported schemas, unsafe entrypoint artifact names, unknown options, duplicate options, unknown inputs, and noncanonical field values.

The output directory contains `source-plan.json`, `runtime-config.json`, `ledger.params`, native keys and circuits, serialized initial/predicted state, deployment/call intents, and `native-contract.json`. Witness-bearing files use mode 0600. Keep the directory private. Each assembly invocation randomizes the deployment address, so keys, address, state, and intents must stay together.

The transaction runner refuses the wrong genesis, funds through the published local development identity, requires finalized matching receipts, checks accepted state against predicted state, and verifies invalid witnesses and replay rejection. Its accepted evidence is `local/native-localnet.json`.

The standalone checks are also reusable:

```sh
node scripts/zkir/check-native-cases.mjs build/native-claim/artifacts build/native-claim/artifacts/initial-state.bin negative
node scripts/zkir/check-native-cases.mjs build/native-claim/artifacts build/native-claim/local/observed-state.bin replay
```

The current helper supports the initial source subset: Native-field and Boolean inputs, field arithmetic, equality, eager selection, Poseidon, state-cell reads, and empty initial maps with member checks and insertion. Unsupported source features must fail before a support claim. The accepted source-to-ledger evidence is [native-localnet.md](native-localnet.md).
