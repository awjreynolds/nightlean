# Scalar decoding from bounded bytes

`fromBytes(Native, value)` and `fromBytes(JubjubScalar, value)` accept Source byte strings from zero through 1024 bytes. Both interpret the full input as a little-endian integer and reduce modulo the requested field. The existing `fromBytes32` and `foreignFromBytes` APIs stay available.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit decodeChallenge where
  private digest : Bytes 64
  output challenge : Native := disclose(jubjubScalarToNative(
    fromBytes(JubjubScalar, digest)))
end
```

The disclosure marks the derived scalar as a public output. The decoder carries the digest's private origin until this release.

## Target field and byte order

For a byte array `b`, the decoded integer is `b[0] + 256*b[1] + 256²*b[2] + …`. Native reduces modulo the BLS12-381 scalar field modulus. JubjubScalar reduces directly modulo the Jubjub subgroup order.

Reducing through Native first changes the answer for some inputs. Noctium emits the native ZKIR `from_bytes` instruction for the selected target. The Rust evaluator uses the original bytes for the matching modular reduction.

This operation reduces scalar encodings. It does not establish canonical signature encodings or verify a signature. Signature helpers must enforce their scheme's scalar, point and message rules. The strict Jubjub point decoder remains `fromBytes32(JubjubPoint, value)`.

## Empty inputs and limits

An empty input decodes to typed zero after evaluating its operand. Assertions inside an empty operand still run. The compiler emits no invalid typed Bytes0 input or decoder operation. Private origins survive the conversion, including for empty values.

Byte lengths above 1024 and targets other than Native or JubjubScalar reject. The existing foreign decoder covers the separate Secp and Curve25519 families.

## Evidence

[Issue 80](https://github.com/awjreynolds/noctium/issues/80) tracks implementation. [ScalarFromBytes.lean](../../tests/ScalarFromBytes.lean) covers direct modulo semantics, retained 32-byte equivalence, maximum length, target validation and disclosure. [The native case](../../runtime/tests/scalar_from_bytes.rs) checks the emitted relation, full-width reduction, empty-input assertions and committed returns.

The 67-job compiler/Claim build, source fixture, producer inventory/negative guards, guide snippet and legacy 3.2.0 runtime library compilation pass. One native case covers both target fields at lengths 0, 32, 64 and 1024 in 0.03 seconds. Altered byte values, changed committed output, invalid lengths and each false empty-operand assertion reject. The retained field/scalar/strict-point conversion case passes in 0.04 seconds. One focused host/control case checks direct and helper operation routes, target/length validation and typed zero defaults.

The entrypoint has 4,342 instructions, 1,090 native inputs and six output fields. Its six `from_bytes` instructions include shared 32-byte conversions, both 64-byte conversions and both 1024-byte conversions. No native Bytes0 reconstruction is emitted. These counts establish no K or proving-time comparison.

No new keys, proofs, deployments or K/proving-time benchmark qualify this conversion slice. Signature library APIs and full source/native preservation remain separate work.
