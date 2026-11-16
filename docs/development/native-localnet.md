# Native private claim accepted on localnet

On 2026-11-16, the actual `examples/PrivateClaim.lean` source compiled through Nightlean's Lean frontend, typed circuit/state model, native entrypoint lowerer, and symbolic Impact plan exporter. Native runtime helpers assembled ledger artifacts, the official final ZKIR 3.2.0 tool generated keys, and the isolated ledger accepted deployment and a private one-time claim. This route invokes no Compact compiler, runtime, source adapter, or generated contract bindings.

## Accepted evidence

The machine-readable evidence is [native-localnet-receipts.json](native-localnet-receipts.json).

- Contract address: `dc6910da6b30913df3670122d8abbf9512bded7e8711062e7e1bbabb73442d43`.
- Deployment ledger transaction: `0xfe234f7f10ca1822b11b779cbcd9b66ac18e6bf569efb215b137163dd3ced027`, finalized block 398, block hash `0x3c9c0924b8fab4a4797b1de66a93e5646adcfb8e38e0724eea9206f8b21c4bb6`.
- Claim ledger transaction: `0xa81671aac5baa1a03aaa7fd13ac4fa4e829287e996f5bc020fdcd98ddec53c16`, finalized block 401, block hash `0x667a0e08c0e51226482c2c807bc14fffe15d167069728c9e5b9e788a16cdfa95`.
- Both receipts contain exact matching `TxApplied` and contract events under extrinsic index 4. The observer verifies the development genesis, runtime, canonical finalized block, exact transaction hash, contract address, and `midnight.sendMnTransaction` call.
- The fetched accepted public state matches the native predicted state byte for byte. SHA-256: `d03deaed2a47e077412acd4db0fb3069e47cd41d05472eebb3c8182f0c938dc3`.
- Serialized claim transaction SHA-256: `9f4eada8cdbb6d7c53ae3ee009c610e01a12c5d6c0007368ce0fc52fdf9adbc0`.

The network is `undeployed`, genesis `0x823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d`, runtime `2001100`, transaction version `4`. Funding uses the published synthetic development identity on Nightlean's isolated chain.

## Source and toolchain provenance

The compiled Lean source SHA-256 is `5a2e0f2f8b087567d00a274bc64bfb893b4ddf70fb459923ccd2db05be1bf771`. The source-generated symbolic plan SHA-256 is `cbb84324fa64596fcf076b6fe8dd566ad5956a82ce1e04682e030bc1b7c14242`. The native entrypoint ZKIR SHA-256 is `c569dd887fdf6aa3bdd2c8e2358985657ad3612eb72e0eb16f28682bb2b2b81c`.

The independent official ZKIR CLI was built from revision `446c7fecc6bd41dab99ebe89ab404e9d077d11a9` using Rust 1.100.0 and the upstream lockfile. Its native Darwin ARM64 binary SHA-256 is `2664d4d6f97c04e882b4208b9926f27f1e1d03082ca508e69f0145c491aa694a`. The bootstrap records source, lockfile, Rust version, command, binary version, and digest.

Native key generation reports `k=9`, 297 rows. Prover key SHA-256: `b9b7e5dd38f01468aecf6b698a74905800227a41e3ca7d7ef302dc287fc64e55`. Verifier key SHA-256: `bc1e417d74922fee9a97778a0a00e7f9910e38f356cba94aa2dee0788b3fa536`. The final official ZKIR WASM checker accepts the preimage. Proof server 9.0.0 generates and self-verifies a 3,852-byte diagnostic contract proof. Transaction funding generates a separate proof bound to the final transaction.

## Invalid witnesses and replay

Before deployment, the official checker rejected five separate altered cases: secret, Merkle sibling, path direction, public root, and supplied nullifier. Every rejection was `Failed direct assertion`, and the immutable initial native state stayed unchanged.

After the valid transaction finalized, the runtime loaded the fetched accepted native state and attempted the same claim. Its expected absent-nullifier read conflicted with the spent map and failed. A second node-state fetch proved replay left state unchanged. The replay test performs no transaction submission after this failed native execution.

Additional runtime checks reject noncanonical field strings, wrong boolean input types, unknown input names, and references hidden in an unselected expression arm. Source expressions use eager selection to match the Lean reference semantics and ZKIR lowering.

## Reproduction

Follow [native-contract.md](native-contract.md) for the complete source-driven commands and [the localnet guide](../../scripts/localnet/README.md) for the isolated services. Keep artifacts from one assembly invocation together because deployment addresses include randomness. Public development fixture values come from `scripts/zkir/claim-config.mjs`; actual witness files belong outside tracked source.

The successful run used actual parameters captured from this development node, SHA-256 `d412f77763b2cb7d1f5260fdad837750b66321d486a5babed4b786cd52c5a43b`. Recapturing parameters later changes fee-price data as the chain advances, so the parameter digest is observation-specific.

## Binding requirements established by execution

The native entrypoint binds one activity group per VM operation and includes the mandatory communication commitment. Runtime assembly uses the actual ledger cost model and `partitionTranscripts` to obtain valid guaranteed/fallible budgets. Setting the transcript's gas to measured query cost alone caused an earlier node rejection for insufficient guaranteed execution budget. The official partitioner fixed this, and the final native call finalized.

This qualifies the selected source subset and private-claim workload on the isolated local ledger. Broader feature coverage and production assurance remain separate work.
