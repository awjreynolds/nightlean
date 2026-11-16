# Native contract assembly and proof experiment

`scripts/zkir/native-contract.mjs` constructs native ledger contract artifacts
from the Lean entrypoint relation and Impact fixture. This route does not call
Compact or load a generated Compact JavaScript contract.

The experiment registers the native verifier key in `ContractOperation`, builds
the root/campaign/spent-map state in `ContractState`, constructs `ContractDeploy`,
and serializes deployment and call intents. `ContractCallPrototype` carries the
exact native VM transcript, private witness outputs, empty explicit call input
and output, and communication randomness.

## Reproduce

Generate the fixtures using [the direct Impact procedure](direct-impact.md),
then run these commands from the repository root. Set `ZKIR_V3` to the pinned
native ZKIR binary. The checked native binary is version 3.2.0-rc.2 from the
official Compact 0.36.0 distribution, invoked directly for key generation.

```sh
"$ZKIR_V3" compile build/direct-impact/claim.zkir build/direct-impact/claim.prover build/direct-impact/claim.verifier
node scripts/zkir/native-contract.mjs build/direct-impact/operations.json build/direct-impact/claim.zkir build/direct-impact/claim.prover build/direct-impact/claim.verifier build/native-contract
NIGHTLEAN_PROOF_SERVER=http://127.0.0.1:16300 node scripts/zkir/native-contract.mjs build/direct-impact/operations.json build/direct-impact/claim.zkir build/direct-impact/claim.prover build/direct-impact/claim.verifier build/native-contract --prove
```

The proof option requires the isolated Nightlean proof server and its official
public parameters. The script restricts the server URL to loopback because the
payload includes witness values. Each invocation creates a new randomized
deployment address and overwrites the matching output files. Keep the address,
state, and intents from the same invocation together.

## Observed results

The native key generator compiled the direct claim/state relation with k=9 and
297 rows after the binding fixes below. The final ZKIR 3.2.0 implementation accepted its proof preimage. The
native verifier key round-tripped through `ContractOperation` serialization.

On 2026-11-16 the isolated proof server returned HTTP 200 with a 3,852-byte
proof. The native proving pipeline verifies the generated proof before returning
success. The proof SHA-256 for that run was
`efd5a14d731fef1dc66d2a6dc5057f243386d45eba97de4528667531441ad76b`.
Proofs use randomness, so repeated runs produce different bytes.

The first transaction-level attempt exposed an activity-group requirement:
the ledger consumes one ZKIR activity result for each native VM operation.
Binding the entire flattened transcript in one group passed preprocessing and
standalone proving but caused the native toolkit to run out of activity entries.
The lowerer now emits 21 Impact groups for the fixture's 21 operations, and both
native harnesses assert this correspondence. The corrected relation serializes
to 2,610 bytes. The earlier proof observation describes the bounded experiment
before this transaction-binding fix, rather than evidence for node acceptance.

A subsequent transaction-level proof was generated but failed final verification
because the relation omitted the communication commitment. The pinned ledger
verifier always builds public inputs beginning with binding input and
communication commitment, followed by the encoded operation fields. Native
contract entrypoints now enable that commitment. This adds 22 rows to the
corrected relation. Standalone circuit artifacts keep their separate flag.

The native contract operation serialized to 1,362 bytes. The deployment intent
serialized to 1,809 bytes and the call intent to 1,581 bytes in that run. The
script writes `initial-state.bin`, `predicted-state.bin`, `deploy-intent.bin`,
`call-intent.bin`, `keys/claim.prover`, `keys/claim.verifier`, `zkir/claim.zkir`,
`zkir/claim.bzkir`, and a machine-readable `native-contract.json` report.

## Remaining transaction boundary

This script performs native artifact assembly, VM execution, official
preprocessing, and optional cryptographic proving. It does not fund, balance,
sign, or submit a transaction. The standalone proof uses binding input 42 for
this bounded experiment. A final transaction requires its own binding and proof
construction and must not reuse this proof as an attached contract-call proof.

The call intent contains a guaranteed transcript assembled from native query
costs. Qualification still requires transaction-level partitioning and fee
budget checks, a funded deployment, a proof bound to the final transaction, and
node acceptance with the expected state change. Preview acceptance is a separate
network result. The script reports `transactionSubmitted: false` until those
steps occur through another runner.

Native API references are the locked `@midnight-ntwrk/ledger-v9` 1.0.2 typings
and the official [ledger 9 runtime implementation](https://github.com/midnightntwrk/midnight-ledger/tree/ledger-9.1.0.1/onchain-runtime-wasm/src).
