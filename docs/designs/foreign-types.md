# Foreign-field implementation plan

Status: implementation in progress under [issue 75](https://github.com/awjreynolds/noctium/issues/75). The current source snapshot does not qualify these types. This package extends [the full native capability goal](../compatibility/GOAL.md), after native hash-to-curve.

The first dependency is implemented: [Lean metadata and field constant encoding](../../Noctium/Foreign.lean), a [checked Rust native codec](../../runtime/src/foreign.rs), and [shared differential vectors](../../runtime/tests/fixtures/foreign-codec/321/encoding.json). The focused native case covers all six types, canonical boundary values, identity/generator points and malformed encodings. The Rust module is currently exposed only with `zkir-321`. Source Ty/IR, operations, transport and SDK integration remain pending. This foundation adds no source opcode/type coverage, keys, proofs or deployment qualification.

## Scope and interface

Implement Secp256k1 and Secp256r1 together, each with Base, Scalar and Point. Add Curve25519 next. Preserve existing Native and Jubjub source, artifact and host encodings.

Use a closed foreign-curve family and family-parameterized base/scalar/point types. Expose explicit source type names for each family. Centralize native type names, field moduli, encoding layouts, compressed-byte lengths and supported operations in one Foreign module. Keep Native/Bool/UInt policy separate. Reject mixed curves and mixed Base/Scalar operands.

Reuse the pinned native `IrValue` and public instruction helpers behind a checked Rust ForeignValue interface. That interface owns canonical decode/encode, byte conversion and typed operation evaluation. Do not implement curve arithmetic or SEC1 decoding again in the SDK.

## Canonical representation

The selected source is ZKIR 3.2.1 revision `7a51b3385bbf4bce3604df87a7c70867c9ab43c0`, with circuits 7.3.0 from the matching ledger pin.

Foreign field Encode is not ordinary integer serialization. For field value x and modulus p, the encoded integer is `(x - 1) mod p`. Encode packs its low 192 bits and high 64 bits into two Native fields. Both limb bounds and the combined canonical range matter.

A Secp point uses EncodeBase(x), EncodeBase(y), and an identity flag, totaling five Native fields. Identity uses EncodeBase(0) twice and flag one. Those coordinate limbs are not zero. Reuse `decode_offcircuit` and its final re-encode comparison. Bare `from_public_input` is insufficient as a canonical validator.

Field `from_bytes` interprets little-endian bytes and reduces modulo the selected field order. Field `to_bytes` yields canonical 32-byte little-endian data. These conversions have different semantics from canonical field transport.

Secp compressed points occupy 33 bytes. Native identity uses 33 zero bytes. Decoding must enforce the exact native round trip. Affine extraction rejects identity, and affine construction does not create identity. Source point semantics must represent identity explicitly.

Curve25519 uses two Native fields for Base/Scalar and four for Point. Its point and subgroup rules require their own implementation package.

## Operations and integration

Base/Scalar: constants, canonical transport, add, subtraction through add/neg, mul, neg, nonzero inv, equality, selection and byte conversions.

Point: identity/constants, canonical transport, add, neg, equality, selection, matching-scalar multiplication, generator multiplication, affine construction/extraction and compressed byte conversions.

Use typed native inputs for new foreign values and Encode for transcript projections and results. Preserve Native/Jubjub paths. Symbolic terms must bind curve, role and ordered operands. Producer facts must distinguish foreign validity from bounds on encoded Native limbs. Never use the Native modulus as the foreign value's range.

Source and authoring own Foreign metadata, Ty/IR, semantic oracles, validation, disclosure, frontend and helper syntax. Backend owns typed inputs, aliases, projections, normalization, producer validation, lowering and guarded totalization. Runtime/SDK owns checked ForeignValue, logical types, canonical host/provider transport, transcript field counts and native execution.

## Minimum checks

One focused source/native fixture should exercise both Secp families across Base, Scalar and Point, including zero/one encodings, generator multiplication, identity and compressed-byte round trips. Necessary negatives cover family mismatch, noncanonical field/limb encodings, altered identity coordinates/flags, off-curve or noncanonical compressed points, zero inversion and identity coordinate extraction. Guarded inactive partial operations must stay total.

Follow the existing minimum-check policy. No new proof/key generation or deployment campaign per primitive. Broad formal witness reconciliation remains in [issue 21](https://github.com/awjreynolds/noctium/issues/21).

Primary implementation references: pinned `zkir/src/ir_types.rs`, `zkir/src/ir_instructions/{encode,from_bytes,to_bytes,from_coordinates,into_coordinates,ec_mul,inv,select}.rs`, circuits `field/foreign/field_chip.rs` and `ecc/foreign/weierstrass_chip.rs`.
