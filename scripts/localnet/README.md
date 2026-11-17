# Isolated Noctium development chain

The launcher uses the cached released Midnight node, native Rust toolkit, Proof Server 9, Indexer 4.4.101, and official Node.js relay images. The relay uses only Node's TCP API. Native contract funding and submission invoke the Rust toolkit executable. These commands do not invoke a source-language compiler or JavaScript contract adapter. The launcher creates only `nightlean-dev` containers and an internal network with the same name. Existing AuthZK containers and chains stay untouched.

```sh
node scripts/localnet/stack.mjs up
npm ci --prefix scripts/preview
node scripts/preview/wallet-local.mjs
```

Host endpoints bind loopback only:

| Service | URL |
| --- | --- |
| Node HTTP RPC | `http://127.0.0.1:19944` |
| Node WebSocket RPC | `ws://127.0.0.1:19944` |
| Proof server | `http://127.0.0.1:16300` |
| Indexer GraphQL | `http://127.0.0.1:18088/api/v4/graphql` |
| Indexer WebSocket | `ws://127.0.0.1:18088/api/v4/graphql/ws` |

The public development genesis is `0x823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d`. The qualified runtime is `2001100`, transaction version `4`, network `undeployed`. The launcher checks the genesis and waits for node block one, proof-server health, and indexer readiness. Each container has a two-CPU and 3 GiB limit. The proof server allows two concurrent jobs.

The writable proof parameter cache defaults to `/private/tmp/nightlean-proof-params`. The shared AuthZK cache is never mounted writable. Set `NIGHTLEAN_PROOF_CACHE` to another dedicated cache directory to run elsewhere. To bootstrap from public parameter files already verified by the pinned official toolchain, supply read-only source directories:

```sh
NIGHTLEAN_PROOF_CACHE_SOURCE=/path/to/verified-public-parameters \
NIGHTLEAN_PROOF_CACHE_EXTRA_SOURCE="$HOME/.cache/midnight/zk-params" \
node scripts/localnet/stack.mjs up
```

The launcher copies missing parameter files into Noctium's own directory, including dereferencing any source links. It checks the qualified k9 parameter's SHA-256 before starting. Other parameters must come from a source you have already verified. All image digests are pinned in `stack.mjs`. Docker must already contain those images. The launch command uses `--pull never` and does not download a replacement.

Missing parameter files triggered an `os error 30` when an earlier setup mounted the incomplete shared cache read-only. The repaired server uses the dedicated writable cache, with the missing k9 copied from the official native compiler's verified cache. To apply a cache repair while keeping the node and indexer's chain state:

```sh
node scripts/localnet/stack.mjs restart-proof
```

The development chain includes a publicly known seeded wallet. On 2026-11-16, the wallet helper synchronized to protocol `2001100` and observed `250000000000000` raw NIGHT units, `1250000000000000000000000` raw DUST units, and five available DUST coins. These are disposable local balances and do not fund Preview.

Stop and remove only this localnet with:

```sh
node scripts/localnet/stack.mjs down
```

Removing the containers discards their development-chain state. Keep the chain running while another agent uses the endpoints.

Observe an exact finalized deployment or call independently from toolkit exit status:

```sh
node scripts/localnet/receipt.mjs TX_HASH CONTRACT_ADDRESS ContractDeploy FROM_BLOCK
node scripts/localnet/receipt.mjs TX_HASH CONTRACT_ADDRESS ContractCall FROM_BLOCK
```

The observer uses the SDK helper's locked Polkadot API install. Set `NIGHTLEAN_WALLET_DEPENDENCIES` if that install lives outside `scripts/preview`. It requires the exact local genesis and runtime, a canonical finalized block, one matching ledger `TxApplied`, a matching contract event in the same extrinsic, and `midnight.sendMnTransaction`. A partial ledger outcome fails. The initial private-claim receipts are recorded in [`localnet-receipts.json`](../../docs/development/localnet-receipts.json).

The setup follows the released local profile inspected in the sibling AuthZK project, especially `backend/preprod/release-smoke.mjs` and `backend/adapter/local.mjs`. Public upstream references: [Ledger 9](https://docs.midnight.network/relnotes/ledger-9), [proof-server installation](https://docs.midnight.network/getting-started/installation), and [local wallet funding](https://docs.midnight.network/guides/node-server-wallet).

## Native private-claim workflow

The actual Lean source now completes a native deployment and accepted claim on this chain. Build the independent official ZKIR CLI, capture real ledger parameters, and use the source-generated plan to assemble native contract artifacts. The full command sequence is in [native-contract.md](../../docs/development/native-contract.md). No source-language adapter or generated contract JavaScript participates.

The runtime config generator produces public development fixture values and five explicit invalid cases. The native runner checks those cases, funds and submits deployment and claim intents, requires exact finalized events, compares the fetched ledger state to the predicted state, and rejects replay against the accepted spent-nullifier map.

The accepted native receipts and state digest are recorded in [native-localnet.md](../../docs/development/native-localnet.md) and [native-localnet-receipts.json](../../docs/development/native-localnet-receipts.json).

To replace only the TCP relay with the pinned official Node image while preserving the node, proof server, indexer, and chain state, run `node scripts/localnet/stack.mjs restart-relay`.
