# Shielded coin map comparator

The Compact 0.36.1 fixture uses language 0.28 and runtime 0.21.0. Its compiler source pin is `7fa3a117c5e7efe9d2c51da04263e5f0b3509144`. The comparison profile pairs with Midnight Ledger 9.1.0.1. The contract follows the private tip jar receive path. It rejects an existing nonce, calls `receiveShielded(disclose(coin))`, then inserts the coin into `Map<Bytes<32>, QualifiedShieldedCoinInfo>` under the nonce with `kernel.self()` as recipient.

The focused oracle compiles with `--skip-zk` and checks the in-memory Compact runtime. A store-only circuit on a fresh context fails with `Coin commitment not found` and leaves both the receive effects and map empty. A successful call records one shielded receive and one output to the contract. The map stores the submitted `nonce`, `color`, and `value` plus `mt_index: 0n`, resolved from that call's newly created output. A second call with the same nonce fails before it records another receive.

Run with the pinned compiler and runtime directories:

```sh
node tests/compact/shielded-coin-map.mjs /path/to/compactc-0.36.1 /path/to/compact-runtime-0.21.0
```

The in-memory Compact check uses a synthetic `ShieldedCoinInfo`. The Noctium localnet run below exercises proof generation and transaction acceptance.

The pinned Ledger runtime books output commitments before a contract call. The query context exposes the assigned index in its commitment table. The receive effect claims the commitment, and the Map write reads the index from the context and appends it to the stored coin value. A native VM probe ran the same operation sequence with context indices `0` and `42`. It stored the corresponding index and rejected a missing commitment without changing the input state or effects.

The Compact-generated Map write uses `Dup 5` to reach the context for this top-level Map. The vendored `Map_insert_coin!` fragment expands to `Dup 4` for the same path and fails the native probe with `ExpectedCell(null)`. The checked operation sequence uses the generated stack offset. [Native receive and Map qualification](https://github.com/awjreynolds/noctium/issues/205)

Noctium exposes this path as `receiveShieldedToMap(pot, disclose(nonce), disclose(color), disclose(amount))`. The native fixture checks the emitted ZKIR 3.2.1 and Impact transcript, including index 42 supplied by the query context. It also checks duplicate and missing commitments without a funded transaction.

```sh
lake exe noctium compile tests/ShieldedReceive.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output build/shielded-receive
NOCTIUM_SHIELDED_RECEIVE_DIR="$PWD/build/shielded-receive" \
  cargo test --locked --manifest-path runtime/Cargo.toml \
  --no-default-features --features zkir-321 --test shielded_receive -- --include-ignored
```

## Funded Noctium localnet receipt

The Lean fixture mints five units and receives one contract-owned output in the same guaranteed section. The Rust host books its index against the finalized Zswap state, proves the contract call and output, and funds fees from the development DUST wallet. Before funding, the host rechecks the booking and the initial contract state against the latest finalized snapshot.

Ledger 9.1.0.1 finalized the call at block 140. The stored coin matched the nonce, color, value and Ledger index 29. The native host rejected missing and mismatched offers before submission and checked the Map remained unchanged. The ZKIR 3.2.1 circuit used k=13 and 6,646 rows. Wallet-funded transfers remain open. [Receipt](shielded-receive-localnet-receipt.json)

Compile `tests/FundedShieldedReceive.lean` with the ZKIR 3.2.1 target above and select `FundedShieldedReceive.tip.zkir` and its Impact plan in the bundle recipe. Generate keys with the pinned ZKIR CLI and use the isolated node's Ledger parameters. [Bundle setup](portable-artifacts.md) · [Localnet setup](../../scripts/localnet/README.md)

```sh
NOCTIUM_RECEIVE_NODE=http://127.0.0.1:19944 \
NOCTIUM_RECEIVE_PARAMETER_CACHE=/path/to/verified/dust/zswap-and-srs-cache \
NOCTIUM_RECEIVE_BUNDLE=/path/to/funded-receive-bundle \
NOCTIUM_RECEIVE_MANIFEST_SHA256=YOUR_MANIFEST_SHA256 \
  cargo test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  funded_shielded_receive_localnet -- --ignored --nocapture
```

## Whole-coin spend from a Map

`tests/ShieldedSpend.lean` defines two entries. `tip` mints and receives five units into the Map. `spend` consumes the recorded coin, derives its nullifier and a commitment to one user-owned output, then removes the old key. The native host builds the spend proof from the coin's assigned index and the finalized Zswap tree. The Compact runner also checks the exact effects, output nonce, Map removal and replay rejection for a deterministic full-value send.

Ledger 9.1.0.1 finalized this native spend at block 372. The recipient decrypted the five-unit output at Ledger index 29, and the finalized Map no longer contained the input coin. The harness rejected a mismatched nonce and a replay before submission. The spend circuit used k=14 and 12,770 rows. [Receipt](shielded-spend-localnet-receipt.json)

Compile the fixture with the 3.2.1 target and create separate authenticated `ShieldedSpend.tip` and `ShieldedSpend.spend` bundles. Use the same source, profile and ledger parameters for both. [Bundle setup](portable-artifacts.md)

```sh
NOCTIUM_TRANSFER_NODE=http://127.0.0.1:19944 \
NOCTIUM_TRANSFER_PARAMETER_CACHE=/path/to/verified/parameter-cache \
NOCTIUM_TRANSFER_TIP_BUNDLE=/path/to/tip-bundle \
NOCTIUM_TRANSFER_TIP_MANIFEST_SHA256=YOUR_TIP_MANIFEST_SHA256 \
NOCTIUM_TRANSFER_SPEND_BUNDLE=/path/to/spend-bundle \
NOCTIUM_TRANSFER_SPEND_MANIFEST_SHA256=YOUR_SPEND_MANIFEST_SHA256 \
  cargo test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  funded_shielded_map_spend_localnet -- --ignored --nocapture
```

## Partial spend from a Map

`tests/ShieldedMapPartialSpend.lean` adds `sendShieldedFromMap`. It spends one contract-owned coin into a user output and contract change. The native runtime enforces `0 < sendAmount < inputAmount`, derives the user nonce with `midnight:kernel:nonce_evolve` and the change nonce with `midnight:kernel:nonce_evolve/2`, removes the old Map row, then receives the change under its derived nonce. The native plan binds the nullifier and both output commitments, and allows only read-only change-key checks before the change receive.

The pinned Compact 0.36.1 runner checks a 5-unit input split into a 2-unit user output and 3-unit contract change, including exact claim hashes, Map contents, amount bounds and replay rejection. Noctium's focused VM test and opt-in compiled-plan/ZKIR check pass against the same vector. On the ZKIR 3.2.1 mock, sharing the immutable contract-address read changes the circuit size from 25,493 rows to 19,599 rows. Both versions report k=15.

Ledger 9.1.0.1 finalized the split at block 231. The recipient decrypted two units at output index 32. The contract Map held three units at change index 33 and no longer held the original coin. The harness rejected a mismatched nonce, a full-value request through the split entry and replay before submission. [Receipt](shielded-partial-spend-localnet-receipt.json)

Export the Lean fixture:

```sh
lake exe noctium compile tests/ShieldedMapPartialSpend.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/experiments/214/lean-partial-spend-shared-address
```

Run the Compact comparator with the pinned compiler and runtime directories:

```sh
node tests/compact/shielded-coin-map.mjs \
  /path/to/compactc-0.36.1 \
  /path/to/compact-runtime-0.21.0
```

Run the funded Noctium localnet test after preparing authenticated `tip` and `spend` bundles and a local development node:

```sh
NOCTIUM_PARTIAL_SPEND_NODE=http://127.0.0.1:19944 \
NOCTIUM_PARTIAL_SPEND_PARAMETER_CACHE=/path/to/verified/parameter-cache \
NOCTIUM_PARTIAL_SPEND_TIP_BUNDLE=/path/to/tip-bundle \
NOCTIUM_PARTIAL_SPEND_TIP_MANIFEST_SHA256=YOUR_TIP_MANIFEST_SHA256 \
NOCTIUM_PARTIAL_SPEND_SPEND_BUNDLE=/path/to/spend-bundle \
NOCTIUM_PARTIAL_SPEND_SPEND_MANIFEST_SHA256=YOUR_SPEND_MANIFEST_SHA256 \
  cargo test --locked --manifest-path runtime/Cargo.toml --lib \
  --no-default-features --features zkir-321,localnet \
  funded_shielded_map_partial_spend_localnet -- --ignored --nocapture
```

Pins and source behavior: [Compact 0.36.1 release](https://github.com/LFDT-Minokawa/compact/releases/tag/compactc-v0.36.1), [Compact private tip jar](https://docs.midnight.network/tutorials/private-tip-jar/smart-contract), [Compact ledger ADTs](https://docs.midnight.network/compact/reference/ledger-adt), [Ledger 9.1.0.1](https://github.com/midnightntwrk/midnight-ledger/releases/tag/ledger-9.1.0.1).
