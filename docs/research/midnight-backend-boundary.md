# Midnight backend boundary for a Lean frontend

Context pointer: [ticket 01, Map the deployable Midnight backend boundary](../../.scratch/lean4-midnight-compiler/issues/01-midnight-backend-boundary.md)

Research checked on 2026-11-16 against official Midnight documentation and repositories.

## Findings

- The documented contract build path accepts Compact source and an output directory. The generated bundle contains ZKIR circuits, prover and verifier keys, JavaScript and TypeScript contract bindings, and a compiler JSON description. Midnight.js deployment then pairs the generated contract module with those compile artifacts. [Build a private smart contract](https://docs.midnight.network/guides/build-a-private-smart-contract) [Deploying and operating a contract](https://docs.midnight.network/guides/deploy-and-operate)
- `midnight-zkir` publicly defines the ZKIR format, VM, and CLI. Its `zkir compile-many` command turns `.zkir` files into prover and verifier keys. The repository describes ZKIR as the circuit format targeted by Compact's compiler. The reviewed official docs do not document a complete direct-ZKIR route that also produces the generated contract bindings and other artifacts used by Midnight.js deployment. [midnight-zkir repository](https://github.com/midnightntwrk/midnight-zkir)
- The current public-network compatibility set is ledger 9, Compact toolchain 0.36.0, language version 0.28.0, Compact runtime 0.21.0, on-chain runtime 4.0.0, and proof server 9.0.0. Compact 0.36 generates ZKIR version 3. [Compatibility matrix](https://docs.midnight.network/relnotes/support-matrix) [Ledger 9 upgrade](https://docs.midnight.network/relnotes/ledger-9) [Compact 0.36 release notes](https://docs.midnight.network/relnotes/compact/toolchain-0.36.0)
- ZKIR and the on-chain runtime are separate components. Midnight's ledger 9 notes list the on-chain runtime as version 4.0.0, while Compact 0.36's release notes describe ZKIR version 3 as its backend. [Ledger 9 upgrade](https://docs.midnight.network/relnotes/ledger-9) [Compact 0.36 release notes](https://docs.midnight.network/relnotes/compact/toolchain-0.36.0)
- Contract artifacts are version-sensitive. Compact 0.36 changes verifier keys when recompiling contracts that used ZKIR v2. A deployed contract needs matching keys, supplied through its maintenance authority, or it needs redeployment. Compact 0.36 also requires Compact runtime 0.21.x. [Compact 0.36 release notes](https://docs.midnight.network/relnotes/compact/toolchain-0.36.0)

## Recommendation

For v1, generate Compact source from the supported Lean subset and pass it to the pinned official Compact toolchain. This reuses the documented route for producing circuits, keys, generated contract bindings, and compiler metadata. Treat this as a source-generation integration, not as an official third-party frontend API. Keep direct ZKIR or Impact VM output out of the v1 promise until an end-to-end artifact and deployment interface is documented and versioned.

The main risk is semantic drift: the Lean frontend must preserve Compact's ledger, witness, disclosure, and circuit semantics. The output must pin the full compatible toolchain and runtime set, because matching only the ZKIR version does not identify all required contract artifacts.
