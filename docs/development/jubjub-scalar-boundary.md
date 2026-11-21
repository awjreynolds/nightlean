# Jubjub scalar conversion boundary

Compact 0.36.1 and runtime 0.21.0 reduce an explicit `Field as JubjubScalar`
conversion modulo the Jubjub subgroup order before generator multiplication.
The focused comparator checks raw values `7` and `q + 7`, where
`q = 6554484396890773809930967563523245729705921265872317281365359162392183254199`.
Both produce `7G` with coordinates:

- x: `47805549206756120863994733988949966563868680443409072344285414365387721651928`
- y: `10883866336127360287053583923937114185802477515052223349661086820822299756070`

Noctium already expresses this boundary with
`jubjubScalarFromNative(raw)`. Its Lean evaluator and native runtime reduce the
`Native` value modulo `q`, and the 3.2.1 relation checks the resulting scalar
and point coordinates. The source conversion stays explicit. This does not
change typed `JubjubScalar` input decoding, storage, equality, or signatures.
The existing `runtime/tests/jubjub.rs` rejection for typed `q + 7` remains in
place.

Reproduce the source artifact and paired checks with:

```sh
lake build noctium
lake exe noctium compile tests/JubjubScalarBoundary.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/experiments/289/jubjub-scalar-boundary
node tests/compact/jubjub-scalar-boundary.mjs \
  /path/to/compactc-0.36.1 /path/to/compact-runtime-0.21.0
NOCTIUM_JUBJUB_SCALAR_BOUNDARY_DIR="$PWD/build/experiments/289/jubjub-scalar-boundary" \
  cargo test --locked --offline --no-default-features --features zkir-321 \
  --test jubjub_scalar_boundary \
  native_explicit_field_reduction_matches_compact_generator_multiplication \
  -- --ignored --exact
```
