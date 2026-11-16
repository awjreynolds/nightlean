# Preview wallet preparation

This helper creates a Nightlean-only wallet, prints its public Preview address, and optionally checks its unshielded balance. It never prints the seed or submits a transaction.

Install and run:

```sh
npm ci --prefix scripts/preview
node scripts/preview/wallet.mjs
node scripts/preview/wallet.mjs --balance
```

The default wallet directory is `/private/tmp/nightlean-preview-wallet`, with directory mode `0700` and seed mode `0600`. Set `NIGHTLEAN_WALLET_DIR` to a durable private directory before the first invocation if the wallet must survive temporary-directory cleanup. Reuse the same directory for every run. Do not copy the seed into the repository.

The faucet is <https://midnight-tmnight-preview.nethermind.dev/>. Submit the printed `mn_addr_preview` address and complete its CAPTCHA. The official procedure requires an unshielded address. After funding, NIGHT still needs registration for DUST generation before contract deployment. This read-only helper does not perform registration.

The helper pins Wallet SDK `2.0.0`, uses the Preview network and the SDK's ledger-v9-native fork schedule, and contacts the public Preview indexer. Balance output reports only confirmed, synchronized unshielded holdings. An empty object means no confirmed unshielded token balance.

Full facade synchronization and DUST registration use the same private seed:

```sh
node scripts/preview/wallet-full.mjs
node scripts/preview/wallet-full.mjs --register-dust
```

The first command only synchronizes. The second submits registration only when funded unregistered NIGHT UTXOs exist, after the SDK estimates the fee and waits for enough retroactive DUST. Keep a local proof server running, with `NIGHTLEAN_PROOF_SERVER` set if its URL differs from `http://127.0.0.1:16300`. The Preview wallet must finish its full history sync before registration. On 2026-11-16 the empty project wallet reached protocol `2001100`, with zero NIGHT and DUST. Registration and deployment were not attempted.

For the separate funded development chain, use `wallet-local.mjs` after starting the [Nightlean localnet](../localnet/README.md). This identity belongs to the published development genesis and must never be used on Preview or another public network. The local helper verifies the exact genesis and runtime before deriving the public test identity.

Sources: [Preview endpoints](https://docs.midnight.network/relnotes/network), [funding and DUST registration](https://docs.midnight.network/guides/acquire-tokens), and [Wallet SDK 2.0.0](https://docs.midnight.network/relnotes/wallet/wallet-sdk-2-0-0). Some funding-guide code examples still pin SDK 1.2.0. Use the installed 2.0.0 interfaces rather than copying those examples unchanged.

Read-only readiness checks use the existing project wallet without creating a seed, registering DUST, or submitting transactions:

```sh
node scripts/preview/preflight.mjs --toolkit-identity --artifacts /path/to/compiled/contract
```

The preflight checks Preview RPC and indexer connectivity, loopback proof-server health, key artifact presence, the existing wallet's exact NIGHT asset balance and DUST balance. The optional toolkit identity check mounts the seed file read-only into the pinned toolkit with networking disabled and compares only its public unshielded address against the SDK address. The secret never enters host command arguments or output. Docker access is required for this optional check. The overall operation has a 120 second deadline.

On 2026-11-16, the preflight verified matching SDK/toolkit addresses, synchronized the full wallet to protocol `2001100`, and observed no confirmed NIGHT and zero DUST. [The public result](../../docs/development/preview-preflight-2026-11-16.json) records the checks. Funding must precede DUST registration and generation. Preview transaction building, fee estimation, submission, and receipt verification still need to run with the funded identity. A successful health check or positive balance does not establish successful deployment.

Toolkit root seeds and SDK master seeds both enter BIP32 derivation. The reviewed native [HD helper](https://github.com/midnightntwrk/midnight-node/blob/2d855f597c6b4de9630cab69d8b55ad39d71663a/ledger/helpers/unsafe/src/ledger_9/wallet/hd.rs) places Schnorr NIGHT at `m/44'/2400'/0'/0/0`, DUST at role 2, and Zswap at role 3. The installed SDK 2.0.0 follows the same default account and role paths. The pinned-image public-address comparison verifies the NIGHT identity rather than assuming compatibility from similar APIs.
