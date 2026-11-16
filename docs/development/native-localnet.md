# Native artifact localnet qualification

Checked 2026-11-16. This experiment targets the same isolated development ledger as the completed private-claim adapter path. The compiler's Lean ZKIR emitter, native runtime operations, keys, contract state, ContractOperation, ContractDeploy, ContractCallPrototype, and Intent are assembled without Compact.

The generated artifacts originate from `scripts/zkir/native-contract.mjs`. The local-only funding and submission harness is `scripts/localnet/deploy-native.mjs`. The latter refuses any genesis except the pinned published development chain, funds through its public seeded development identity, and requires independent finalized `TxApplied` plus the corresponding contract event.

## First native deployment

Command:

```sh
NIGHTLEAN_WALLET_DEPENDENCIES=/private/tmp/nightlean-preview-wallet node scripts/localnet/deploy-native.mjs /private/tmp/nightlean-native-contract /private/tmp/nightlean-native-local
```

The direct native contract deployment was accepted and finalized:

- Contract address: `bb5a07cb09a83dceff850e3bfee389ff9f9d2aed9a21bfea8cf44644b6b5247d`.
- Ledger transaction hash: `0xf0494fc80f2b1acd5502c469ce02e635d863da15b787ce47d956269678befa02`.
- Finalized block: 203, block hash `0x6c28a1107e60a6acf06fac66e5114b7fe88e4cc8446e9b5a7f3dd830a036c592`.
- Extrinsic index: 4.
- Extrinsic hash: `0x2b23ff1aa844a7be6858baef245366e251799d41c8cb49041ee201928c72d879`.
- Matching events: `TxApplied` and `ContractDeploy`.

This establishes language-independent deployment of the native state and verifier-key operation. It does not establish an accepted call for this first circuit revision.

## First call boundary and repair

Official native preprocessing accepted the call, but the toolkit's transaction proof builder failed at ledger `prove.rs:284` with `range start index 1 out of range for slice of length 0`. The failure occurred before the call transaction was created or submitted.

Source inspection found the compiler had bound the entire VM program with one ZKIR `impact` instruction. The checker therefore returned one activity/skip entry. The transaction builder requires one such entry per VM operation and consumed the metadata once per operation. The bounded repair preserves the exact program field sequence but emits a separate ZKIR impact instruction for each VM operation. The replacement circuit needs regenerated keys and a new contract deployment.

The complete successful private-claim localnet evidence remains in [localnet-claim.md](localnet-claim.md). This native experiment is an additional route qualification, not a replacement for the accepted evidence.

## Final bounded retry

The compiler repaired per-operation activity metadata and enabled the communications commitment for contract entrypoints. Ledger verification always includes the communication commitment after the binding input, so omitting this circuit input caused the intermediate revision's final transaction proof check to fail. Standalone circuit lowering keeps its separate commitment policy.

The corrected native contract deployed and finalized again:

- Contract address: `0897cddc6b6543ede0724a649ad5931571da9aff2ea367a058940b641a245a51`.
- Deployment transaction hash: `0xd263fea5c2a3e59b3231a7605f759782d4e38d830c019b33ad0f7e4fec082fd3`.
- Finalized block: 255, block hash `0x6328c6d8f5c4e383619c432e7107c9e8e58899a9f52abb7787b1ed8da911a2c1`.
- Extrinsic index: 4, extrinsic hash `0x4e028244e35e49bdcf35f14280cdd17897d03757be789578d4a3623cad376933`.
- Matching events: `TxApplied` and `ContractDeploy`.

The official toolkit then generated and cryptographically checked the complete native call transaction. Submission reached the node, which rejected transaction `0x8de41e8269ddded4e6d4c4407de4d2ce7afdaf03335737fec3cb45de7cee8b11` with custom error 104. The node log states the precise reason: `guaranteed execution would fail: ran out of gas budget`.

This revision attached the entire program as guaranteed execution. The remaining native route work is to partition and budget guaranteed/fallible transcripts using actual ledger parameters, then repeat the accepted-call and replay checks. No native call acceptance is claimed. The transaction was rejected by the mempool before inclusion.

The successful POC route remains the Lean-generated packaging adapter, whose exact deployment, accepted claim, invalid witnesses, and replay evidence are recorded separately. The direct route now has native deployment, native VM state execution, full transcript preprocessing, proof generation and verification, and transaction construction evidence, with its remaining gate identified at node gas-budget validation.
