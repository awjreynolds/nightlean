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

## Read the ledger caller

`readCaller as (present, isContract, contractId, userId)` binds two
Boolean flags and two `Bytes32` addresses. A contract caller sets both
flags and fills `contractId`. A user caller sets only `present` and
fills `userId`. An absent caller or inactive guard yields false flags
and zero bytes. A private guard needs disclosure.

The native ledger context supplies the caller. The Impact plan checks
the presence, tag and active address against the ZKIR statement. A
different ledger caller fails the same transcript check. The Rust SDK
ordinary-call path prepares an absent caller. Midnight derives a
top-level user caller only in the relevant unshielded-input context, and
support for deriving that value during SDK preparation needs separate
qualification. [Midnight caller semantics](https://docs.midnight.network/compact/reference/ledger-adt#caller)

[Lean fixture](../../tests/NativeCaller.lean) ·
[Compact oracle](../../tests/compact/caller.mjs) ·
[Native checker](../../runtime/tests/native_caller.rs)

The Rust SDK finalized the deployment at Ledger 9.1.0.1 localnet block
67 and the active top-level call at block 70. Exact state bytes matched
the prediction. A separate decoder verified that the `recorded` cell
changed from true to false. The relation measured K9 and 312 rows. The
contract and user variants ran in the native VM and Compact runtime.
[Localnet receipt](native-caller-localnet-receipt.json)

## Record standalone token mints

```lean
when enabled mintShielded(domain, disclose(amount))
when enabled mintUnshielded(domain, disclose(amount))
```

Both effects take a 32-byte domain and a `UInt 64` amount. The domain, amount
and guard must be public or explicitly disclosed. Active effects accumulate by
domain in separate shielded and unshielded mint maps. Accumulation beyond
`UInt 64` fails. The ledger derives each token type from the issuer address
and domain. These effects record issuance. A transfer or settlement requires
its own ledger effects and transaction outputs.

The [Lean fixture](../../tests/NativeStandaloneMints.lean) and
[Compact reference fixture](../../tests/compact/StandaloneMints.compact)
exercise guarded minting, separate effects and the accumulation limit.

The [localnet receipt](native-standalone-mints-localnet-receipt.json) records
an active call with two mint amounts, 17 and 2, in each namespace. Ledger
9.1.0.1 finalized the call with the predicted contract state. The transaction
settled no tokens to a recipient.

## Read the current contract address

`readSelf as own` binds the executing contract's `Bytes32` address.
`when enabled readSelf as own` produces zero bytes when inactive. A
private guard needs disclosure before it controls this public read.
The compiler encodes the query-context address as a native Impact read
and binds its two byte limbs in ZKIR. [Midnight self reference](https://docs.midnight.network/compact/reference/ledger-adt#self)

The address comes from the contract execution context. This allows a
caller-dependent entrypoint to use the callee's own address alongside
the separate caller value. Native replay against a different address
fails the equality check. [Lean fixture](../../tests/NativeContractAddress.lean) ·
[Compact oracle](../../tests/compact/contract-address.mjs) ·
[Native checker](../../runtime/tests/native_contract_address.rs)

The Rust SDK deployed the fixture on Ledger 9.1.0.1 localnet at block 47
and finalized the active call at block 50. The full state matched the SDK
prediction, and a separate decoder matched the stored `lastAddress`
cell to the actual deployment address. Native sizing reported K8 and
146 rows. The guarded skip and wrong-address replay ran in the native
VM. [Localnet receipt](native-contract-address-localnet-receipt.json)

## Read a token balance

Use a 32-byte color and a Boolean tag. `true` selects the unshielded balance and
`false` selects the shielded balance for the same color.

```lean
tokenBalance(color, isUnshielded) as amount
tokenBalanceLt(color, isUnshielded, limit) as below
tokenBalanceGt(color, isUnshielded, limit) as above
```

These operations read the balance at the start of the call. A missing token has
balance zero. Exact reads return `UInt 128`. Both strict comparisons accept a
`UInt 128` limit at the source boundary. The pinned Impact VM requires the
actual balance and limit to fit in `UInt 64` when the comparison runs.

Color, tag, comparison limit and any `when` guard are public or explicitly
disclosed. A skipped exact read binds zero. A skipped comparison binds
`false`. The comparison binds its Boolean result to the native transcript.
Use the exact read when the application needs the amount.

The [Lean fixture](../../tests/NativeTokenBalance.lean) and
[Compact reference fixture](../../tests/compact/TokenBalance.compact) use the
same inputs and guards.

The [localnet receipt](native-token-balance-localnet-receipt.json) records a
finalized ordinary call for an absent unshielded token. The call wrote zero
over the previous recorded value of 17. Shielded and nonzero cases use
simulated starting balances with the pinned native checker.

## Settle tagged token inputs and outputs

```lean
incUnshieldedInputs(color, received, isUnshielded)
incUnshieldedOutputs(color, sent, isUnshielded)
claimUnshieldedCoinSpend(color, authorized, isUnshielded, isContract, recipient)
```

Each operation records a separate native effect. The ledger verifies these
effects against the transaction's other calls and settlement data.
Use `true` for the unshielded token tag and `false` for the shielded tag.
The spend's recipient tag distinguishes a contract address from a user
address with the same bytes. Each operand and any guard is public or
explicitly disclosed.

A first entry accepts a `UInt 128` amount. An addition to an existing entry
requires both operands and their sum to fit `UInt 64` in the pinned VM.
The [Lean fixture](../../tests/NativeTaggedSettlement.lean) and
[Compact reference fixture](../../tests/compact/TaggedSettlement.compact)
exercise these bounds and the effects' tagged keys.

The [funded localnet receipt](native-tagged-settlement-localnet-receipt.json)
records a proof which checks that both starting balances are zero, even after
the source records receipt effects. The finalized state contains 17
unshielded-tag units and 23 shielded-tag units of the same color. The native
assembler predicted both balances. The finalized bytes matched the SDK's
ledger replay byte for byte.
