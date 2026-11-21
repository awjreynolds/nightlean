# Shielded coin map comparator

The Compact 0.36.1 fixture uses language 0.28 and runtime 0.21.0. Its compiler source pin is `7fa3a117c5e7efe9d2c51da04263e5f0b3509144`. The comparison profile pairs with Midnight Ledger 9.1.0.1. The contract follows the private tip jar receive path. It rejects an existing nonce, calls `receiveShielded(disclose(coin))`, then inserts the coin into `Map<Bytes<32>, QualifiedShieldedCoinInfo>` under the nonce with `kernel.self()` as recipient.

The focused oracle compiles with `--skip-zk` and checks the in-memory Compact runtime. A store-only circuit on a fresh context fails with `Coin commitment not found` and leaves both the receive effects and map empty. A successful call records one shielded receive and one output to the contract. The map stores the submitted `nonce`, `color`, and `value` plus `mt_index: 0n`, resolved from that call's newly created output. A second call with the same nonce fails before it records another receive.

Run with the pinned compiler and runtime directories:

```sh
node tests/compact/shielded-coin-map.mjs /path/to/compactc-0.36.1 /path/to/compact-runtime-0.21.0
```

The in-memory check needs no funded wallet or native transaction host. It accepts a synthetic `ShieldedCoinInfo` and does not establish that a paid coin exists or that a proof and transaction pass ledger validation. Full on-ledger qualification requires the funded local native transaction host, proof server, and an accepted Ledger 9.1.0.1 receipt.

Pins and source behavior: [Compact 0.36.1 release](https://github.com/LFDT-Minokawa/compact/releases/tag/compactc-v0.36.1), [Compact private tip jar](https://docs.midnight.network/tutorials/private-tip-jar/smart-contract), [Compact ledger ADTs](https://docs.midnight.network/compact/reference/ledger-adt), [Ledger 9.1.0.1](https://github.com/midnightntwrk/midnight-ledger/releases/tag/ledger-9.1.0.1).
