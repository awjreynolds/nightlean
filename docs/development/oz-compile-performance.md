# OpenZeppelin confidential-token compilation benchmark

Measured on 2026-11-18. Noctium currently compiles this large workload substantially more slowly than Compact. This is a baseline for optimization, not a speed claim.

![Measured compiler performance](../assets/noctium-performance.png)

## Source compilation

Apple M3 Max, 16 logical cores, 48 GiB RAM. Compilers were prebuilt, dependencies were warm, each run used a fresh process and output directory. Setup/download time, key generation, proving and deployment are excluded.

| Compiler | Three runs (seconds) | Median | Peak observed RSS |
| --- | --- | --- | --- |
| Noctium `adbc42c`, Lean 4.35.0 | 61.350 / 61.811 / 62.504 | 61.811 s | 1.50 GiB |
| Compact 0.36.1, `--skip-zk` | 0.277 / 0.255 / 0.255 | 0.255 s | 0.260 GiB |

These timings cover source processing and emitted artifacts. Noctium emits 16 native entrypoint relations, 13 standalone helper relations, Impact plans and witness/metadata sidecars. Compact emits 15 provable relations, one pure JavaScript function (`computeAccountId`), JavaScript/types and metadata. The workloads have comparable functions but different input/result layouts, explicit state-candidate handling and artifact sets. This is not a proven semantic/ABI equivalence benchmark.

## What the timing includes

The Noctium CLI currently launches two complete Lean frontend passes over the source. The first checks the file before any artifact writes. The second repeats source elaboration and performs artifact export. The exporter also compiles witness programs for standalone and entrypoint artifacts. These are identified repeated-work paths, not a measured phase breakdown. No profiler was run for this benchmark.

The token source declares no contract theorems. Neither timed command generates cryptographic ZK proofs or keys. Lean theorem checking and transaction ZK proof generation are separate operations. This benchmark does not establish functional correctness of the contract or compiler.

## Contract size and functionality

The [Noctium port](../../examples/openzeppelin/ConfidentialToken.lean) contains 1,013 physical lines, 967 nonblank lines excluding full-line comments, 16 entrypoints, 12 public state slots, two private cells and 13 witness/circuit definitions. These source counts exclude imported compiler/library implementation.

The exact [OpenZeppelin wrapper](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/test/integration/_mocks/ComposedConfidentialFungibleTokenPublicSupply.compact) contains 144 lines and imports the 1,512-line [token module](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/token/ConfidentialFungibleToken.compact), the public-supply extension and crypto helpers. Comparing only the 144-line wrapper with the full Lean file would misrepresent source size.

The workload includes ElGamal encrypted balances on Jubjub, pending credits, ECDH memos, account/key registration, transfers, sweeping, mint/burn, delegated escrow spending, allowances, counters, nested maps/lists and private wallet witnesses. The existing isolated-localnet scenario covers all sixteen entrypoints. Nominal ABI and composition qualifications remain separate.

## Native circuit sizes

Both artifact sets were sized using the same pinned native ZKIR 3.2.1 implementation, revision `7a51b3385bbf4bce3604df87a7c70867c9ab43c0`. Its executable banner still says 3.2.0; the recorded source pin and binary SHA identify the selected patch. Sizing uses `mock-compile`, which builds the circuit model without generating keys or proofs.

K belongs to each entrypoint circuit. This contract does not measure K20. Noctium reaches K16, with a largest circuit of 63,125 rows. Source compile time is measured for the entire file, so it cannot be divided into trustworthy per-entrypoint compilation times.

| Entrypoint | Noctium K | Noctium rows | Compact K | Compact rows |
| --- | ---: | ---: | ---: | ---: |
| `registerWithKey` | 13 | 6,932 | 13 | 7,540 |
| `mint` | 15 | 25,236 | 15 | 25,140 |
| `sweep` | 13 | 7,076 | 13 | 7,287 |
| `transfer` | 16 | 41,787 | 16 | 38,002 |
| `_move` | 16 | 41,779 | 16 | 37,994 |
| `burn` | 14 | 16,323 | 14 | 13,825 |
| `clearMemos` | 13 | 6,924 | 13 | 6,573 |
| `totalSupply` | 7 | 66 | 6 | 34 |
| `isRegistered` | 7 | 120 | 8 | 129 |
| `balanceOf` | 9 | 267 | 10 | 901 |
| `pendingOf` | 9 | 267 | 10 | 901 |
| `computeAccountId` | 13 | 2,085 | pure JS | no proof circuit |
| `approve` | 16 | 41,575 | 16 | 38,349 |
| `allowance` | 10 | 513 | 9 | 435 |
| `transferFrom` | 16 | 63,125 | 16 | 62,483 |
| `burnFrom` | 16 | 39,122 | 16 | 38,294 |

Noctium emits 9,039 native instructions across its 16 entrypoint relations. `transferFrom` contains 1,338 instructions, 12 persistent hashes and 16 curve multiplications (seven variable-base and nine generator). Native sizing for all 16 Noctium entrypoints took 11.843 seconds, separate from source compilation. Instruction/row totals across entrypoints count shared functionality more than once. They are complexity descriptions, not a single combined circuit.

## Reproduction and limits

```sh
.lake/build/bin/noctium compile examples/openzeppelin/ConfidentialToken.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --output FRESH_DIRECTORY

compactc --skip-zk \
  contracts/test/integration/_mocks/ComposedConfidentialFungibleTokenPublicSupply.compact \
  FRESH_DIRECTORY

zkir mock-compile ENTRYPOINT.zkir
```

Use fresh output directories and serial timed runs. The Compact compiler ran externally from temporary storage and is not a Noctium build/runtime dependency. The [official release](https://github.com/midnightntwrk/compact/releases/tag/compactc-v0.36.1) archive SHA-256 was verified before execution. Machine-readable runs, hashes and counts are retained in [oz-compile-performance.json](oz-compile-performance.json).

The first Noctium timing sample overlapped one small sizing process; the subsequent two source runs and all Compact runs ran without concurrent benchmark synthesis. RSS was recorded for the last two Noctium runs and all Compact runs. Background system activity was not controlled. No key-generation/proving-time conclusion follows from these source timings or from matching K. Broad compiler optimization remains under [issue 74](https://github.com/awjreynolds/noctium/issues/74).
