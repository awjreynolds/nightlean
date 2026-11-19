# OpenZeppelin confidential-token compilation benchmark

The current OpenZeppelin comparison measures **4.65 s** for Noctium and **0.274 s** for Compact 0.36.1. Both exclude keys and proofs. The Noctium run uses range deduplication and emits ledger and witness artifacts. Compact emits its source artifacts with `--skip-zk`.

![Noctium and Compact benchmark showing compilation time, artifact sizes, and K and rows for all 16 entrypoints](../assets/noctium-performance.png)

## Current compilation and artifact sizes

| Compiler output | Three source runs (s) | Median (s) | Output files | Total bytes | ZKIR bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| Noctium ledger and witness | 4.873 / 4.647 / 4.588 | 4.647 | 53 | 5,805,683 | 758,817 |
| Compact 0.36.1 with `--skip-zk` | 0.274 / 0.286 / 0.274 | 0.274 | 20 | 518,022 | 167,669 |

The three alternating runs used the same Apple M3 Max, prebuilt compilers, warm dependencies, fresh processes and new output directories. Byte counts use the files emitted before sizing. Noctium includes Impact plans and witness sidecars. Compact includes JavaScript, source maps, types and compiler metadata. Noctium emits 16 relations and Compact emits 15. `computeAccountId` is a pure JavaScript function in the Compact build. The ABI, state handling and artifact sets differ. [Machine-readable measurements and hashes](oz-compile-performance.json)

## Historical source compilation

Apple M3 Max, 16 logical cores, 48 GiB RAM. Compilers were prebuilt, dependencies were warm, each run used a fresh process and output directory. Setup/download time, key generation, proving and deployment are excluded.

| Compiler | Three runs (seconds) | Median | Peak observed RSS |
| --- | --- | --- | --- |
| Noctium `adbc42c`, Lean 4.35.0 | 61.350 / 61.811 / 62.504 | 61.811 s | 1.50 GiB |
| Compact 0.36.1, `--skip-zk` | 0.277 / 0.255 / 0.255 | 0.255 s | 0.260 GiB |

These timings cover source processing and emitted artifacts. Noctium emits 16 native entrypoint relations, 13 standalone helper relations, Impact plans and witness/metadata sidecars. Compact emits 15 provable relations, one pure JavaScript function (`computeAccountId`), JavaScript/types and metadata. The workloads have comparable functions but different input/result layouts, explicit state-candidate handling and artifact sets. This is not a proven semantic/ABI equivalence benchmark.

## Single-pass Noctium follow-up

| OpenZeppelin port, ZKIR 3.2.1 | Wall | User CPU | System CPU |
| --- | ---: | ---: | ---: |
| Two Lean passes, `7643dc6` | 65.94 s | 62.96 s | 1.40 s |
| One Lean pass | 41.29 s | 39.51 s | 0.71 s |
| One Lean pass and witness compilation reuse | 38.90 s | 35.46 s | 0.83 s |

The combined changes saved 27.04 seconds (41%) in one matched run per version on the same M3 Max. The exporter reused 10 compiled witness plans when binding them to ledger entrypoint relations. All three runs generated 93 byte-identical files totaling 7,697,562 bytes. The CLI publishes the bundle directory after Lean exits successfully with a manifest. A late source error or early exit leaves no output directory or staging files, and a nonempty destination stays untouched. [Optimization issue](https://github.com/awjreynolds/noctium/issues/85)

## Reuse the Impact plan during export

The exporter now writes the Impact plan returned by the checked ZKIR lowerer. The native producer still derives its expected schedule independently from the pruned source. This removes one repeat of Impact lowering for each of the port's 16 entrypoints.

One before-and-after pair on the same M3 Max emitted all 93 files byte for byte, totaling 7,697,562 bytes. The baseline at `8a697a1` used 34.79 s of user CPU and the revised exporter used 34.72 s. Elapsed time was 41.76 s and 36.32 s respectively. The near-identical user CPU and the single pair leave the speedup unestablished. Identical relations preserve the existing K values. [Circuit-size issue](https://github.com/awjreynolds/noctium/issues/74)

## Exact range-check deduplication

The initial `--dedup-range-checks` pass kept the first unconditional check for each SSA operand and width. On the OpenZeppelin port, it removed 402 repeated checks across 11 of 29 emitted relations. Impact plans matched byte for byte. Witness bindings referenced the corresponding relation in each build.

| Changed entrypoint, ZKIR 3.2.1 | Checks removed | Default rows | Deduplicated rows | K in both builds |
| --- | ---: | ---: | ---: | ---: |
| `_move` | 42 | 41,779 | 39,175 | 16 |
| `approve` | 50 | 41,575 | 38,475 | 16 |
| `burn` | 20 | 16,323 | 15,083 | 14 |
| `burnFrom` | 27 | 39,122 | 38,258 | 16 |
| `transfer` | 42 | 41,787 | 39,183 | 16 |
| `transferFrom` | 41 | 63,125 | 61,813 | 16 |

The pinned `mock-compile` measured 2.1% to 7.6% fewer rows across these entrypoints. The pinned native checker gave the same results for 34 scalar cases in both modes, including acceptance at 255 and rejection at 256 when narrowing to eight bits. One serial full compile per mode took 36.57 and 35.69 seconds respectively, with nearly identical CPU time. These runs did not measure proving time. Generate fresh proving and verifier keys for any changed relation. [Circuit-size issue](https://github.com/awjreynolds/noctium/issues/74)

The current opt-in pass also removes a wider check when an earlier unconditional check already constrains the same operand. On this port, seven more 248-bit checks follow a 128-bit check on the same value. The pass removes 409 checks in total across 11 relations. Pinned synthesis reports 62 fewer rows in each affected ledger entrypoint (`_move`, `approve`, `burn` and `transfer`). For example, `transfer` drops from 39,183 to 39,121 rows and stays at K16. Impact files remain byte-identical and all 34 raw-witness cases agree with the default compiler.

Lean checks `RangeDedup.preserves_decoded` against the actual JSON pass and the independent scalar ZKIR decoder. For instruction lists accepted by that decoder, the optimized list also decodes, preserves ordered non-range instructions, and has the same satisfying assignments. The model covers the scalar decoder's instruction set. The ZKIR verifier, expanded instruction set and ledger execution require separate evidence. [Preservation theorem](../../Noctium/Verification/RangeDedup.lean)

## Reuse identical byte selections

Byte chunks now reuse the same exact-operand selector cache as scalars. The compiler still lowers both arms, including any assertions they contain. The cache compares the selector and both ordered SSA operands. [ZKIR lowerer](../../Noctium/Backend/Zkir.lean)

Nine of the token port's 16 ledger relations emitted fewer selectors. The pinned ZKIR 3.2.1 tool measured the following changes with the opt-in range pass disabled.

| Entrypoint | Selectors before → after | Rows before → after | K before → after |
| --- | ---: | ---: | ---: |
| `allowance` | 41 → 33 | 513 → 505 | 10 → 9 |
| `transferFrom` | 35 → 25 | 63,125 → 63,115 | 16 → 16 |
| `NativeBytes.inspect` | 18 → 6 | 1,137 → 1,108 | 11 → 11 |

The 16 token Impact plans matched byte for byte. The fresh byte fixture passed both branches and the altered-result rejection in the native checker. The fresh token allowance relation passed the existing token workload's empty and populated allowance checks. These measurements cover circuit sizing. Proving latency and fresh deployments of the changed token relations remain unmeasured. [Issue 74](https://github.com/awjreynolds/noctium/issues/74)

## Remove zero-seed arithmetic from byte packing

The byte packer starts from the highest byte in each nonempty chunk. Previously it multiplied zero by 256 and added the highest byte. The independent producer still checks the packed expression, input bounds and ordered transcript. [ZKIR packer](../../Noctium/Backend/Zkir.lean) · [Source normalization](../../Noctium/Backend/NativeMeaning.lean)

| Workload | Instructions before → after | Rows before → after | K |
| --- | ---: | ---: | ---: |
| Byte pack and reverse | 761 → 754 | 1,144 → 1,137 | 11 |
| Byte storage including Bytes1024 | 4,809 → 4,767 | 11,608 → 11,567 | 14 |
| Token `sweep` | 517 → 513 | 7,076 → 7,073 | 13 |
| Token `transfer` | 1,247 → 1,242 | 41,783 → 41,779 | 16 |
| Token `transferFrom` | 1,328 → 1,322 | 63,115 → 63,110 | 16 |

The comparison starts at `b8b469c`, with `--emit ledger --emit witness` and the default range-pass setting. Pinned `mock-compile` reported fewer rows in 14 of 16 token relations. All Impact plans matched byte for byte. The native byte pack test accepted the regenerated relation and rejected a forged result. The scalar CSE fixture emitted identical bytes. A single token compile in each mode took 4.70 s and 4.68 s. This establishes a small circuit-size reduction. Proof time and funded deployment fall outside this measurement. [Byte packing test](../../runtime/tests/native_byte_packing.rs) · [Issue 74](https://github.com/awjreynolds/noctium/issues/74)

## Reuse existing byte leaves

Static slices select byte leaves directly when the inputs already use that
representation. The two-byte result in `inspectPayment` also avoids serializing
each range-checked byte as a full field. Pinned ZKIR 3.2.1 `mock-compile` measured
the following changes.

| Entrypoint | Rows before | Rows after | K before → after |
| --- | ---: | ---: | ---: |
| `NativeBytes.inspect` | 1,137 | 1,067 | 11 → 11 |
| `readPayment` | 298 | 275 | 9 → 9 |
| `inspectPayment` | 1,545 | 1,194 | 11 → 11 |
| `inspectPayment` with range-check removal | 1,194 | 730 | 11 → 10 |
| `inspectPayment` with comparison reuse added | 730 | 352 | 10 → 9 |

The current `--dedup-range-checks` option applies both range optimizations. The
comparison pass keeps two distinct `less_than` gates and replaces 63 repeated
gates with copies. It uses the same ordered SSA operands and bit width, and
keeps the output names and all assertion sites. The independent producer
validates the optimized relation. The six aggregate native cases pass,
including altered-frame rejection. The sizing run excludes key generation
and proving. [Issue 74](https://github.com/awjreynolds/noctium/issues/74)

A matched OpenZeppelin token run on the same M3 Max compiled all 16 ledger
entrypoints and witness artifacts in 4.75 s with the flag off and 4.67 s with
it on. `transferFrom` used 63,110 and 61,798 rows respectively at K16. The
Impact files matched exactly. The token had no repeated bounded comparisons
for the new pass to remove. These two runs measure one pair, with no
established compile-time change.

## Selected ledger outputs

One serial run per mode on the same host compared a full compile with `--emit ledger --emit witness`. Both runs used the same executable, source and ZKIR 3.2.1 profile.

| Compiler outputs | Wall | User CPU | System CPU | Files | Bytes |
| --- | ---: | ---: | ---: | ---: | ---: |
| All | 35.64 s | 34.79 s | 0.68 s | 93 | 7,697,562 |
| Ledger and witness | 32.21 s | 31.42 s | 0.62 s | 53 | 5,868,886 |

The selected run saved 3.43 seconds (9.6%) and 1,828,676 bytes (23.8%). It retained all 16 entrypoints and ten ledger witness pairs. ZKIR and witness bytes matched. The selected plans removed only the unused standalone file property. The compiler manifest records the emitted paths and roles. [Compiler output roles](portable-artifacts.md#select-compiler-outputs)

## Precompiled Lean frontend

A CPU sample of the OpenZeppelin compile showed Lean's IR interpreter among the busiest active frames. The CLI now loads the native shared library built by Lake when Lake reports a current artifact. The interpreter handles missing and stale builds. Both paths use the same source elaboration and compiler checks. [Lake library builds](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/) · [CLI frontend](../../Noctium/Cli.lean)

| OpenZeppelin port, ZKIR 3.2.1, ledger and witness | Wall | User CPU | System CPU |
| --- | ---: | ---: | ---: |
| Before native library loading, `03ebadf` | 32.02 s | 31.20 s | 0.69 s |
| CLI with Lake-checked native library | 6.01 s | 4.14 s | 0.87 s |

These are two serial runs on the same M3 Max with warm dependencies. All 53 files matched byte for byte, including 16 native relations. The reduction was 81.2% in wall time. The shared library measured 14.6 MB on macOS. Source timing excludes building the compiler, generating keys and producing proofs. The earlier Compact timing used a different output set and appears in the historical baseline above.

## Reuse checked source sizes

Helper analysis now reuses the source-size results from program preparation.
The compiler still checks the weighted expansion budget and checks the expanded
source after lowering a finite range. Three matched OpenZeppelin runs on the
same M3 Max took 4.89, 4.64 and 4.74 s before this change, and 6.05, 4.68 and
4.62 s after. All 53 compiler artifacts matched byte for byte across the
matched runs. The timings establish no material throughput improvement.
The CPU sample put ZKIR's linear common-subexpression lookup among the busiest
Noctium functions. Its representation also appears in the lowering theorems.

## What the timing includes

The older Noctium baseline ran two complete Lean frontend passes. The first checked the source. The second elaborated it again and exported artifacts. The follow-up times these workflows end to end.

The token source declares no contract theorems. Neither timed command generates cryptographic ZK proofs or keys. Lean theorem checking and transaction ZK proof generation are separate operations. This benchmark does not establish functional correctness of the contract or compiler.

## Contract size and functionality

The [Noctium port](../../examples/openzeppelin/ConfidentialToken.lean) contains 1,013 physical lines, 967 nonblank lines excluding full-line comments, 16 entrypoints, 12 public state slots, two private cells and 13 witness/circuit definitions. These source counts exclude imported compiler/library implementation.

The exact [OpenZeppelin wrapper](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/test/integration/_mocks/ComposedConfidentialFungibleTokenPublicSupply.compact) contains 144 lines and imports the 1,512-line [token module](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/token/ConfidentialFungibleToken.compact), the public-supply extension and crypto helpers. Comparing only the 144-line wrapper with the full Lean file would misrepresent source size.

The workload includes ElGamal encrypted balances on Jubjub, pending credits, ECDH memos, account/key registration, transfers, sweeping, mint/burn, delegated escrow spending, allowances, counters, nested maps/lists and private wallet witnesses. The existing isolated-localnet scenario covers all sixteen entrypoints. Nominal ABI and composition qualifications remain separate.

## Native circuit sizes

Both artifact sets were sized using the same pinned native ZKIR 3.2.1 implementation, revision `7a51b3385bbf4bce3604df87a7c70867c9ab43c0`. Its executable banner still says 3.2.0; the recorded source pin and binary SHA identify the selected patch. Sizing uses `mock-compile`, which builds the circuit model without generating keys or proofs.

Compact 0.36.1 also compiled a standalone test contract whose only operation
assigned `disclose(next)` to a `Field` ledger cell. The ordinary compile
generated the prover and verifier keys. Compact's bundled tool and the
independent pinned 3.2.1 tool both sized the emitted relation at K6 and 36 rows.
[Compact release](https://github.com/midnightntwrk/compact/releases/tag/compactc-v0.36.1)

K and rows describe each circuit. The table uses Noctium's range-deduplicated export. Δ rows and Δ % use Compact as the baseline. Seven of the 15 paired circuits use fewer rows with Noctium, and eight use more. Noctium reaches a lower K on three and a higher K on one.

| Entrypoint | Noctium K | Noctium rows | Compact K | Compact rows | Δ rows | Δ % |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `registerWithKey` | 13 | 6,929 | 13 | 7,540 | -611 | -8.1% |
| `mint` | 15 | 25,230 | 15 | 25,140 | +90 | +0.4% |
| `sweep` | 13 | 7,073 | 13 | 7,287 | -214 | -2.9% |
| `transfer` | 16 | 39,113 | 16 | 38,002 | +1,111 | +2.9% |
| `_move` | 16 | 39,105 | 16 | 37,994 | +1,111 | +2.9% |
| `burn` | 14 | 15,017 | 14 | 13,825 | +1,192 | +8.6% |
| `clearMemos` | 13 | 6,921 | 13 | 6,573 | +348 | +5.3% |
| `totalSupply` | 7 | 66 | 6 | 34 | +32 | +94.1% |
| `isRegistered` | 7 | 120 | 8 | 129 | -9 | -7.0% |
| `balanceOf` | 9 | 264 | 10 | 901 | -637 | -70.7% |
| `pendingOf` | 9 | 264 | 10 | 901 | -637 | -70.7% |
| `computeAccountId` | 13 | 2,083 | Pure JS | n/a | n/a | n/a |
| `approve` | 16 | 38,403 | 16 | 38,349 | +54 | +0.1% |
| `allowance` | 9 | 504 | 9 | 435 | +69 | +15.9% |
| `transferFrom` | 16 | 61,798 | 16 | 62,483 | -685 | -1.1% |
| `burnFrom` | 16 | 38,248 | 16 | 38,294 | -46 | -0.1% |

The earlier native sizing and instruction counts are retained in the [machine-readable benchmark](oz-compile-performance.json). Circuit sizing measures synthesis rows and K. It excludes proving latency.

## Reproduction and limits

```sh
.lake/build/bin/noctium compile examples/openzeppelin/ConfidentialToken.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit witness --dedup-range-checks --output FRESH_DIRECTORY

compactc --skip-zk \
  contracts/test/integration/_mocks/ComposedConfidentialFungibleTokenPublicSupply.compact \
  FRESH_DIRECTORY

zkir mock-compile ENTRYPOINT.zkir
```

Use fresh output directories and serial timed runs. The Compact compiler ran externally from temporary storage and is not a Noctium build/runtime dependency. The [official release](https://github.com/midnightntwrk/compact/releases/tag/compactc-v0.36.1) archive SHA-256 was verified before execution. Machine-readable runs, hashes and counts are retained in [oz-compile-performance.json](oz-compile-performance.json).

The first historical Noctium timing sample overlapped one small sizing process; the subsequent two source runs and all Compact runs ran without concurrent benchmark synthesis. RSS was recorded for the last two Noctium runs and all Compact runs. Background system activity was not controlled. No key-generation/proving-time conclusion follows from these source timings or from matching K. Broad compiler optimization remains under [issue 74](https://github.com/awjreynolds/noctium/issues/74).
