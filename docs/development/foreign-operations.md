# Secp arithmetic, points and bytes

The Secp256k1 and Secp256r1 types share typed operations. Family and role stay explicit: a Base value is not a Scalar, and a point uses its own family's Scalar for multiplication.

| Operation | Supported operands and result |
| --- | --- |
| `foreignAdd`, `foreignSub` | Matching Base, Scalar or Point values |
| `foreignNeg` | Base, Scalar or Point |
| `foreignMul`, `foreignInv` | Matching field types; inverse requires nonzero |
| `curveMul` | Point and matching Scalar to Point |
| `curveMulGenerator` | Scalar to its family's Point |
| `curveX`, `curveY` | Nonidentity Point to Base |
| `curveFromCoordinates` | Matching on-curve Base coordinates to Point |
| `foreignToBytes` | Base/Scalar to Bytes32, Point to Bytes33 |
| `foreignFromBytes(TypeName, value)` | Bytes to the chosen foreign type |

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit scaledKey where
  private key : Secp256k1Point
  private factor : Secp256k1Scalar
  let scaled : Secp256k1Point := curveMul(key, factor)
  output encoded : Bytes 33 := disclose(foreignToBytes(scaled))
end
```

Field arithmetic reduces modulo the selected field order. This is separate from bounded UInt arithmetic. Point identity remains a valid typed point, including after multiplying by scalar zero. Coordinate extraction rejects identity.

Field byte conversion uses little-endian integers. `foreignFromBytes` reduces field inputs of length0–1024 modulo the field order, including empty input to zero. Its behavior differs from canonical SDK input transport, which rejects modulo aliases. Points require exactly33 canonical native SEC1 bytes. Identity uses33 zeros.

## Partial operations and disclosure

Zero inversion, identity coordinate extraction, off-curve construction and malformed point decoding reject when active. Discarding the result does not remove those failures. The producer retains explicit nonzero/nonidentity or roundtrip obligations.

Structured inactive guards substitute safe typed values before partial operations. Inverse uses field one, coordinate access uses a nonidentity point, construction uses valid coordinates and point decoding uses canonical identity bytes. An eager `select` evaluates both operands and does not authorize these substitutions.

Private origins flow through arithmetic, points and conversions. Public writes and results still require explicit `disclose`. Native marker writes in the focused example disclose their guard and result independently. The separate [scalar storage package](foreign-storage.md) adds foreign cells and map values.

## Evidence and limits

[ForeignOperations.lean](../../tests/ForeignOperations.lean) exercises both curves and all roles, with typed results, raw64-byte field reduction, empty-input assertions and four independently guarded partial operations. The [native checker case](../../runtime/tests/foreign_operations.rs) compares field results with BigUint modular arithmetic and point results with a separate generator-multiplication route. It checks inactive state preservation, retained empty assertions and each active failure. A focused Rust Session case covers witness evaluation.

Rust reuses the pinned native cryptographic operations. Lean reference semantics uses pure field arithmetic and explicit checked oracle hooks where point computation or compressed decoding needs them. Those assumptions are separate from [whole-language preservation](https://github.com/awjreynolds/noctium/issues/21).

No new keys, proofs or deployment qualify this slice. Foreign map keys and record storage remain work under the [full native goal](../compatibility/GOAL.md).
