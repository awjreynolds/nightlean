# Unsigned source fixture

`plan.json` and `circuit.zkir` are compiler outputs from `examples/BoundedScalars.lean`, entrypoint `BoundedScalars.apply`. They contain no runtime witness values. The source fixture computes `UInt 8` private values' sum with inclusive result maximum 510, exposes `UIntRange 511` publicly, checks an initially zero unsigned cell and writes the result.

The Rust and C++ tests supply synthetic values 255, 255 and public result 510. The official native checker must accept this case and reject a wrong sum or out-of-range input. Fixture regeneration belongs with source/backend changes, followed by the official checker and parent prover/ledger qualification.
