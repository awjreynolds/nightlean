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

The first command only synchronizes. The second submits registration only when funded unregistered NIGHT UTXOs exist, after the SDK estimates the fee and waits for enough retroactive DUST. Keep a local proof server running, with `NIGHTLEAN_PROOF_SERVER` set if its URL differs from `http://127.0.0.1:6300`. The Preview wallet must finish its full history sync before registration. On 2026-11-16 the empty project wallet reached protocol `2001100`, with zero NIGHT and DUST. Registration and deployment were not attempted.

For the separate funded development chain, use `wallet-local.mjs` after starting the [Nightlean localnet](../localnet/README.md). This identity belongs to the published development genesis and must never be used on Preview or another public network. The local helper verifies the exact genesis and runtime before deriving the public test identity.

Sources: [Preview endpoints](https://docs.midnight.network/relnotes/network), [funding and DUST registration](https://docs.midnight.network/guides/acquire-tokens), and [Wallet SDK 2.0.0](https://docs.midnight.network/relnotes/wallet/wallet-sdk-2-0-0). Some funding-guide code examples still pin SDK 1.2.0. Use the installed 2.0.0 interfaces rather than copying those examples unchanged.
