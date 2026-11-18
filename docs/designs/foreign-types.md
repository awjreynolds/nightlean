# Foreign-field implementation plan

Status: implementation in progress under [issue 75](https://github.com/awjreynolds/noctium/issues/75). The current source snapshot covers scoped transport, operations and scalar storage for the six Secp types and three Curve25519 types. Full native qualification remains open. This package extends [the full native capability goal](../compatibility/GOAL.md), after native hash-to-curve.

The codec foundation includes [Lean metadata and field constant encoding](../../Noctium/Foreign.lean), a [checked Rust native codec](../../runtime/src/foreign.rs), and [shared differential vectors](../../runtime/tests/fixtures/foreign-codec/321/encoding.json). [Typed transport](../development/foreign-transport.md) connects all six types to Source Ty/IR, public/private inputs, canonical literals, equality/select and typed results. [Field/group operations and byte conversions](../development/foreign-operations.md) now have focused source/native/witness checks, including active failures and safe inactive guards. The Rust path is exposed only with `zkir-321`; legacy runtime compilation still passes. [Scalar cells and map values](../development/foreign-storage.md) now use canonical multi-field storage. [Curve25519 integration](../development/curve25519.md) now has matching source/native vectors, a witness Session and a native contract case. [Nested scalar tree leaves](../development/foreign-trees.md) now share those encodings. Foreign map keys, record leaves and broader assurance remain pending. No new keys, proofs or deployment qualify these slices.

## Scope and interface

Implement Secp256k1 and Secp256r1 together, each with Base, Scalar and Point. [Curve25519 integration under issue 76](https://github.com/awjreynolds/noctium/issues/76) uses separate Edwards and subgroup rules. Preserve existing Native and Jubjub source, artifact and host encodings.

Use a closed foreign-curve family and family-parameterized base/scalar/point types. Expose explicit source type names for each family. Centralize native type names, field moduli, encoding layouts, compressed-byte lengths and supported operations in one Foreign module. Keep Native/Bool/UInt policy separate. Reject mixed curves and mixed Base/Scalar operands.

Reuse the pinned native `IrValue` and public instruction helpers behind a checked Rust ForeignValue interface. That interface owns canonical decode/encode, byte conversion and typed operation evaluation. Do not implement curve arithmetic or SEC1 decoding again in the SDK.

## Canonical representation

The selected source is ZKIR 3.2.1 revision `7a51b3385bbf4bce3604df87a7c70867c9ab43c0`, with circuits 7.3.0 from the matching ledger pin.

Secp field Encode is not ordinary integer serialization. For field value x and modulus p, the encoded integer is `(x - 1) mod p`. Encode packs its low 192 bits and high 64 bits into two Native fields. Both limb bounds and the combined canonical range matter.

A Secp point uses EncodeBase(x), EncodeBase(y), and an identity flag, totaling five Native fields. Identity uses EncodeBase(0) twice and flag one. Those coordinate limbs are not zero. Reuse `decode_offcircuit` and its final re-encode comparison. Bare `from_public_input` is insufficient as a canonical validator.

Field `from_bytes` interprets little-endian bytes and reduces modulo the selected field order. Field `to_bytes` yields canonical 32-byte little-endian data. These conversions have different semantics from canonical field transport.

Secp compressed points occupy 33 bytes. Native identity uses 33 zero bytes. Decoding must enforce the exact native round trip. Affine extraction rejects identity, and affine construction does not create identity. Source point semantics must represent identity explicitly.

Curve25519 uses two Native fields for Base/Scalar and four for Point. Its Scalar encoding splits at 204 low bits, while Base and point coordinates split at 192. Its point and subgroup rules use their own [implementation package](https://github.com/awjreynolds/noctium/issues/76).

## Operations and integration

Base/Scalar: constants, canonical transport, add, subtraction through add/neg, mul, neg, nonzero inv, equality, selection and byte conversions.

Point: identity/constants, canonical transport, add, neg, equality, selection, matching-scalar multiplication, generator multiplication, affine construction/extraction and compressed byte conversions.

Use typed native inputs for new foreign values and Encode for transcript projections and results. Preserve Native/Jubjub paths. Symbolic terms must bind curve, role and ordered operands. Producer facts must distinguish foreign validity from bounds on encoded Native limbs. Never use the Native modulus as the foreign value's range.

Source and authoring own Foreign metadata, Ty/IR, semantic oracles, validation, disclosure, frontend and helper syntax. Backend owns typed inputs, aliases, projections, normalization, producer validation, lowering and guarded totalization. Runtime/SDK owns checked ForeignValue, logical types, canonical host/provider transport, transcript field counts and native execution.

## Minimum checks

One focused source/native fixture should exercise both Secp families across Base, Scalar and Point, including zero/one encodings, generator multiplication, identity and compressed-byte round trips. Necessary negatives cover family mismatch, noncanonical field/limb encodings, altered identity coordinates/flags, off-curve or noncanonical compressed points, zero inversion and identity coordinate extraction. Guarded inactive partial operations must stay total.

Follow the existing minimum-check policy. No new proof/key generation or deployment campaign per primitive. Broad formal witness reconciliation remains in [issue 21](https://github.com/awjreynolds/noctium/issues/21).

Primary implementation references: pinned `zkir/src/ir_types.rs`, `zkir/src/ir_instructions/{encode,from_bytes,to_bytes,from_coordinates,into_coordinates,ec_mul,inv,select}.rs`, circuits `field/foreign/field_chip.rs` and `ecc/foreign/weierstrass_chip.rs`.
