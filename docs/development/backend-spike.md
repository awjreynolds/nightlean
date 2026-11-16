# Native ZKIR backend spike

Ticket: [Run the first Lean-to-ZKIR vertical slice](https://github.com/awjreynolds/nightlean/issues/9). Checked 2026-11-16. This records actual local experiments, with ledger contract integration still pending.

## Qualified components

- Official final ZKIR 3.2.0 WASM tarball, SHA-256 `06b6b9e00939da4df11f54b7eda0ace3ada4adcff5780ad303db483e2096667b`, from [the release](https://github.com/midnightntwrk/midnight-zkir/releases/tag/zkir-3.2.0). The npm package name is `@midnightntwrk/zkir-v3`.
- Native `zkir-v3` 3.2.0-rc.2, supplied by [Compact 0.36.0 aarch64 Darwin distribution](https://github.com/midnightntwrk/compact/releases/tag/compactc-v0.36.0). Experiments invoke the ZKIR tool directly. Compact source generation is not involved.
- Proof server 9.0.0, official image digest `sha256:5617e26aa76d06c44f4bee667c37eb71ccf02fefe0e5848100fa84001282d515`, verified against [official release metadata](https://github.com/midnightntwrk/midnight-ledger/releases/tag/proof-server-9.0.0). Started as isolated `nightlean-proof-server9` on `127.0.0.1:6300`.
- Official `@midnight-ntwrk/ledger-v9` 1.0.2 for preimage payload serialization and CPU Native-field Poseidon vectors.

## Observed results

A synthetic public-root/private-secret hash relation passed native key generation (`k=5`, 25 rows). A minimal assert relation generated a 3,468-byte proof through the isolated server.

The real Lean-produced `lowererFixture` from `tests/Zkir.lean` passed the final 3.2.0 WASM parser, sizing, binary serialization, and binary deserialization. Native key generation succeeded at `k=7`, 92 rows. The fixture uses private secret 42, private direction 1, public root, and public nullifier. It exercises Poseidon, select, boolean constraints, equality, transcript reads, and public binding.

The CPU vectors for the supported Poseidon layout were:

- `Poseidon([256, 42, 0]) = 41403281693828019283559207914397304973398944634371392995430302730442007581586`.
- `Poseidon([2, 42, 0]) = 26861812985222642461850998877229073475744406667137293942218373188274788972893`.

The valid witness passed the official checker. Changing secret 42 to 43 or increasing the root by one caused `Failed direct assertion`. The valid Lean-produced relation generated a 3,852-byte proof through `/prove`, HTTP 200. Re-running the repository harness generated another 3,852-byte proof. Proof bytes differ because proving uses fresh randomness.

The native proof pipeline calls `verifier_key.verify` before returning success. This gives native cryptographic self-verification, not an independently implemented verifier or ledger acceptance. See pinned [ProofPreimage::prove](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/transient-crypto/src/proofs.rs#L758-L793) and [proof server v3 routing](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/proof-server/src/versioned_ir.rs).

## Reproduction

Install the locked tool dependencies with `npm ci --prefix scripts/zkir --ignore-scripts`. Validate emitted output with `node scripts/zkir/verify.mjs INPUT.zkir OUTPUT.bzkir`. Generate keys with the pinned native binary: `zkir-v3 compile INPUT.zkir KEY.prover KEY.verifier`.

For standalone relation proving, run `node scripts/zkir/prove-relation.mjs INPUT.zkir KEY.prover KEY.verifier WITNESS.json OUTPUT.proof` while the isolated proof server listens on port 6300. The witness file contains decimal-string arrays named `inputs`, `privateTranscript`, `publicTranscriptInputs`, and `publicTranscriptOutputs`, plus decimal-string `bindingInput`. The harness targets the pinned ProofPreimage SCALE encoding. Keep witness files outside tracked source.

The harness rejects noncanonical and out-of-range field values and calls the official checker before the native prover. It fixes the proving URL to loopback because the request contains private witness material.

## Contract binding boundary

The standalone experiments used synthetic public statement vectors. They are not valid Impact call transcripts.

The official `proofDataIntoSerializedPreimage` function extracts public transcript outputs from `Popeq.result`, and public transcript inputs from the field representation of every Impact operation, including opcode and data. A ZKIR `public_input` witnesses a public transcript output. A ZKIR `impact` instruction must bind the actual encoded runtime operations. Binding only a root and nullifier does not establish ledger state access or atomic nullifier insertion. See [pinned runtime preimage construction](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/onchain-runtime-wasm/src/primitives.rs#L227-L279).

Next, compose the typed state-effect plan with a real Impact program, derive its matching ZKIR public-input sequence, assemble a contract operation and verifier key, and run contract transaction verification. Only then qualify a Preview path. Neither keys nor standalone proofs close the vertical-slice ticket.

## Artifact recommendation

Continue with Lean-owned ZKIR and Impact lowering for this workload. The direct circuit tooling and local native proving route are working. Keep the artifact-route decision open until the contract operation, transaction binding, state effects, and ledger acceptance pass. No evidence from this experiment requires using Compact as the source or feature boundary.

## Actual two-level claim and adapter qualification

The emitted `examples/PrivateClaim.lean` relation was then tested. After common-subexpression elimination the official compiler reports `k=8`, 190 rows. Final 3.2.0 WASM serialization is 765 bytes, source SHA-256 `c3a8c9aad701302d54e630961ff159a97e5957e699ae6fc14cc7d5aa78d3395c`, binary SHA-256 `30453aed9917cd95c3cb604849ce06ef51baa8165bb965d2758a041ac9063401`.

The checked fixture uses secret 42, campaign 9, siblings 17 and 23, and direction bits 0 and 1. Its root is `28399696706114328615841781920356350076672934126225635254148383513591039775413`, and nullifier is `16533581147424469099777953019315187868248076859940057971562926865714239641352`. `scripts/zkir/claim-witness.mjs` derives these with the official Native-field CPU implementation and writes a synthetic standalone-relation transcript. The native server generated and self-verified a 3,852-byte proof. Five altered fixtures, changing the secret, sibling, direction, root, or nullifier, all failed official checking with `Failed direct assertion`.

A bounded packaging-adapter check also succeeded. Compiling a pure Compact function containing `transientHash<Vector<3, Field>>([a,b,c])` with official Compact 0.36.0 and invoking the generated pure circuit through Compact runtime 0.21.0 matched Native Poseidon for four vectors: `[1,42,9]`, `[2,17,23]`, `[3,42,9]`, and `[256,42,0]`. This confirms the fixed Field-vector hash layout preserves Nightlean's selected primitive for these vectors. No generic Compact persistentHash encoding is involved.

A Lean-generated Compact adapter is therefore a viable bounded packaging candidate for the implemented Native-field, boolean, selection, and hash workload. It still needs complete claim-level state and call conformance checks before deployment. This result does not make Compact the Nightlean source semantic boundary, establish broader language equivalence, or replace the direct Lean ZKIR emitter.

## Local contract workflow diagnosis

The actual Lean frontend source was compiled with `.lake/build/bin/nightlean compile examples/PrivateClaim.lean --adapter compact --output /private/tmp/nightlean-source-adapter`, then compiled by official Compact 0.36.0. The isolated development ledger accepted its deployment. Five altered private/public cases failed generated contract execution with unchanged ledger state. The first valid call reached native proof-server checking, then proving stopped because the shared public-parameter cache was mounted read-only and lacked the newly required k=9 parameter. The missing parameter already existed in the host's official native compiler cache. This is an environment-cache issue, not a witness or relation rejection. The localnet service owner is preparing a separate Nightlean cache rather than modifying the shared AuthZK cache.

The first TypeScript toolkit bootstrap also exceeded available Docker memory. Setting `NODE_OPTIONS=--max-old-space-size=768` made subsequent invocations complete. A generated witness-config implicit-any error was repaired before deployment.
