# Private one-time claim on the isolated ledger 9 development network

Observed 2026-11-16. This evidence qualifies the local contract path. Preview acceptance remains a separate gate.

## Source and route

The source was `examples/PrivateClaim.lean`, SHA-256 `5a2e0f2f8b087567d00a274bc64bfb893b4ddf70fb459923ccd2db05be1bf771`. The source frontend elaborated its circuit and contract declarations into Nightlean's typed model. Nightlean then emitted an optional Compact packaging adapter while retaining its Lean direct ZKIR backend.

Commands executed from the repository root:

```sh
lake build
.lake/build/bin/nightlean compile examples/PrivateClaim.lean --adapter compact --output /private/tmp/nightlean-source-adapter
/private/tmp/nightlean-backend-spike/compact-native/compactc /private/tmp/nightlean-source-adapter/PrivateClaim.compact /private/tmp/nightlean-backend-spike/source-claim-out
node scripts/localnet/deploy-claim.mjs /private/tmp/nightlean-backend-spike/source-claim-out /private/tmp/nightlean-local-claim4
```

The generated adapter's SHA-256 was `448ea7090f029e2fb8e6974ff8368d61420288561b744585ec6171dc1edc51f6`. The official compiler was Compact 0.36.0, commit `b5d9e4dfc532fe47011c4f6296e254f4853eb469`, language 0.28.0, runtime 0.21.0. The verifier key's SHA-256 was `b6354b0aaf6996b8c882e829910798d1fc2a925521a74175169a16604504d820`.

The bounded hash adapter was checked against Native Poseidon field vectors before this run. Its fixed three-field vector uses the same hash inputs as Nightlean's `poseidon2(domain,a,b)`. This workload's source semantics remain defined by Nightlean and the qualified ledger/proving interfaces.

## Network and transaction evidence

The harness refuses a node whose genesis differs from `0x823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d`. It uses the isolated `nightlean-dev` Docker network, ledger 9.1.0.1 released node/runtime profile, official proof server 9.0.0, and a published development-chain funding identity. No public-network identity or funds participate.

- Contract address: `20a022f70bdab7bd954dea06965c1c3c9bb164a39be132ebff8dba9cf2b915ab`.
- Deployment ledger transaction hash: `0xcfdd250ab451d26e7b01a4ad0534033da0b2149ad6d8d16c496ddb93ca73e230`.
- Claim ledger transaction hash: `0x13c1f6a9c1f3ca11e1d7d918748fddb0c5a79b8986d46a5e1bdb2420343661e2`.
- Serialized claim transaction SHA-256: `56fa3bef0bde1de02a2e20813259c5f6f786e7ed14aedacc6c522d1fcfa83b48`.
- Observed accepted public state SHA-256: `48cd488dc1ea25adee520e1805a3ad2eaf9d8198f3c33347c54d5eefb43cbb80`.

The proof server checked and proved the generated contract call. The native toolkit submitted the transaction. Fetching the contract state from the ledger after submission produced byte-for-byte equality with the predicted successful state, including the spent-nullifier map change.

## Negative cases and replay

Before submitting the valid claim, the harness altered each of five independent values: secret, Merkle sibling, path direction, public root, and supplied nullifier. Each generated contract execution rejected the input. The ledger state remained byte-for-byte equal to the pre-call state after each case.

The valid claim then succeeded. Re-executing the same claim against the accepted state failed with the generated spent-map guard. Fetching state again proved replay left state unchanged. The complete harness returned exit status 0 with `replayRejected: true` and all five negative cases recorded.

The private witness values used for this run are public development fixtures only. Temporary witness JSON, intents, and proving requests remain outside tracked source. The generated transaction and public state alone do not prove the absence of every possible disclosure; source visibility and transcript review remain part of the assurance work.

## Environment repair during qualification

The first native proof attempt reached checking but lacked the k=9 public parameter in a read-only shared cache. The service owner created a separate Nightlean cache and copied the verified public k=9 file downloaded by the official native compiler, leaving the AuthZK cache unchanged. The successful run used the repaired owned proof service. The toolkit's JavaScript heap is bounded to 768 MiB to avoid Docker memory pressure from concurrent local services.

## Remaining gate

This evidence establishes local source-to-contract proof and state acceptance for the selected workload. It does not establish Preview deployment, general source-feature coverage, or complete compiler verification. Keep the vertical-slice ticket open until the same accepted claim runs on Preview using a separately funded Preview identity.

## Finalized event receipts

An independent Polkadot RPC observer then verified both ledger transaction hashes against finalized blocks. Each exact transaction has `midnight.TxApplied` and the matching contract event under the same extrinsic index. Partial application is rejected by the observer.

- Deployment: block 92, hash `0x594486ca9ef319aa7b119a9cc015d76ae1f304dd7c1c56181aa127a7bfefe14f`, extrinsic index 4, extrinsic hash `0x379aa3be5100c3beba44ca91fe54ae00aa390552ae7f827881b7477b624b8ff0`, contract event `ContractDeploy`.
- Valid claim: block 98, hash `0x09282cce44617c484269634b657336e101920b0617bed4bca7ca3c1095b877bb`, extrinsic index 4, extrinsic hash `0x69e5e20d873a5af6043530df9b90e02978a761c2813860ffa598a6d23234db2b`, contract event `ContractCall`.

Reproduce using `NIGHTLEAN_WALLET_DEPENDENCIES=/private/tmp/nightlean-preview-wallet node scripts/localnet/receipt.mjs TX_HASH CONTRACT_ADDRESS ContractDeploy 75` for deployment, or `ContractCall 75` for the claim. The configured dependency directory contains the locked Nightlean wallet SDK's Polkadot API dependency. The observer pins the development genesis and runtime and reads finalized blocks only.
