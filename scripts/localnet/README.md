# Isolated Nightlean development chain

The launcher uses the cached released Midnight node, toolkit, Proof Server 9, and Indexer 4.4.101 images. It creates only `nightlean-dev` containers and an internal network with the same name. Existing AuthZK containers and chains stay untouched.

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

The proof parameter cache defaults to `/private/tmp/authzk-compact036-params`, inspected with the user's authorization. Set `NIGHTLEAN_PROOF_CACHE` to another compatible cache directory to run elsewhere. All image digests are pinned in `stack.mjs`. Docker must already contain those images. The launch command uses `--pull never` and does not download an unreviewed replacement.

The development chain includes a publicly known seeded wallet. On 2026-11-16, the wallet helper synchronized to protocol `2001100` and observed `250000000000000` raw NIGHT units, `1250000000000000000000000` raw DUST units, and five available DUST coins. These are disposable local balances and do not fund Preview.

Stop and remove only this localnet with:

```sh
node scripts/localnet/stack.mjs down
```

Removing the containers discards their development-chain state. Keep the chain running while another agent uses the endpoints.

The setup follows the released local profile inspected in the sibling AuthZK project, especially `backend/preprod/release-smoke.mjs` and `backend/adapter/local.mjs`. Public upstream references: [Ledger 9](https://docs.midnight.network/relnotes/ledger-9), [proof-server installation](https://docs.midnight.network/getting-started/installation), and [local wallet funding](https://docs.midnight.network/guides/node-server-wallet).
