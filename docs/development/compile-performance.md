# Compiler timing snapshot

Measured on 2026-11-16 from an isolated clean archive of published commit `1a972c3032ac9efe55b8f8950ab43c3718cd9b3d`. The host was Darwin arm64 with Lean 4.35.0 already installed. Other development builds ran concurrently. These are small-workload observations, not an idle-machine performance guarantee.

| Workload | Check, median | Compile, median | Compile range |
| --- | --- | --- | --- |
| Actual private one-time claim | 0.97 s | 1.83 s | 1.80–1.88 s |
| Bounded scalar example | 0.90 s | 1.80 s | 1.76–1.86 s |

Each value uses five fresh CLI processes. Compilation includes source elaboration, validation and ZKIR/Impact/metadata emission into a new output directory. It excludes native key generation, transaction proving and the separate contract theorem/export-audit suites. Imports use prebuilt Lean library artifacts. Source bytes were not served from a compiled-example cache.

The clean Nightlean project build took 8.60 s. This is a build of the compiler project against the installed Lean toolchain, not a clean build of Lean or all native dependencies.

[Raw samples and scope](compile-performance.json) preserve every measured run. No matched Compact benchmark was performed, so these results establish no speed advantage. A fair comparison needs semantically matched programs, the same machine/profile and equal treatment of key generation and other output stages. The limited current source feature set also prevents extrapolation to full feature equivalence.

## Repeat the measurement

Use an isolated archive of the recorded commit, run `lake build`, and time the prebuilt `.lake/build/bin/nightlean` executable from that directory:

```sh
/usr/bin/time -p .lake/build/bin/nightlean check examples/PrivateClaim.lean
/usr/bin/time -p .lake/build/bin/nightlean compile examples/PrivateClaim.lean --output build/timing-claim
/usr/bin/time -p .lake/build/bin/nightlean check examples/BoundedScalars.lean
/usr/bin/time -p .lake/build/bin/nightlean compile examples/BoundedScalars.lean --output build/timing-scalars
```

Repeat each command five times, using fresh compile output directories, and report the median plus range. Rebuilding libraries or including key generation measures a different stage and should receive a separate result.
