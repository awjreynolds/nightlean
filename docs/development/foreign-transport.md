# Typed Secp inputs and results

Secp256k1 and Secp256r1 Base, Scalar and Point types support typed inputs, constants, equality, selection and results. [Secp implementation](https://github.com/awjreynolds/noctium/issues/75)

| Source type | Native type | Encoded Native fields |
| --- | --- | --- |
| `Secp256k1Base` | `Base<Secp256k1>` | 2 |
| `Secp256k1Scalar` | `Scalar<Secp256k1>` | 2 |
| `Secp256k1Point` | `Point<Secp256k1>` | 5 |
| `Secp256r1Base` | `Base<Secp256r1>` | 2 |
| `Secp256r1Scalar` | `Scalar<Secp256r1>` | 2 |
| `Secp256r1Point` | `Point<Secp256r1>` | 5 |

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit selectedPoint where
  private point : Secp256k1Point
  private enabled : Bool
  output selected : Secp256k1Point :=
    disclose(select(enabled, point, secp256k1Identity()))
end
```

`private` supplies a witness value for the call. Persisted private state belongs to the host application. A circuit output is a public sink, so releasing a private point requires `disclose`. The annotation authorizes release and does not change the computation or constraints.

Field literals use `secp256k1Base(n)`, `secp256k1Scalar(n)` and their r1 counterparts. They require a canonical integer below the selected modulus. Equality and selection require the same family and role. Native/foreign casts and ordinary Native arithmetic do not coerce foreign values.

Native typed inputs perform canonical foreign decoding. `Encode` expands a Secp field into two Native values and a Secp point into five. Field encoding splits `(x - 1) mod p` into a 192-bit low limb and a 64-bit high limb. Application code should use the typed SDK representation.

## Affine point literals

Use `secp256k1Point(x, y)`, `secp256r1Point(x, y)` or `curve25519Point(x, y)` with literal natural-number coordinates. Noctium checks coordinate bounds and curve membership at compile time. Curve25519 also requires prime-subgroup membership. Use the corresponding `Identity()` constructor for the identity element, including `curve25519Identity()` for the Edwards identity `(0, 1)`.

The ZKIR 3.2.1 target emits a typed `load_constant`. A Secp point carries two encoded coordinates and an identity flag. A Curve25519 point carries two encoded coordinates. Use `curveFromCoordinates` for coordinates computed at runtime.

The source fixture rejects an off-curve Secp point, a curve type mismatch and a Curve25519 point outside the prime subgroup. The Rust case compares all three emitted constants and returned points with the native codec, then checks the Secp256k1 witness control encoding. [Source fixture](../../tests/ForeignPointLiterals.lean) · [Native case](../../runtime/tests/foreign_point_literals.rs)

## Host values

The Rust runtime exposes this path with `zkir-321`. Public/provider JSON uses canonical bytes:

```json
{"kind":"foreign","type":"Secp256k1Scalar","bytes":[1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]}
```

Base/Scalar values use exactly32 little-endian bytes. Points use exactly33 native SEC1 bytes; identity uses33 zeros. Canonical byte transport rejects aliases at or above the field modulus, wrong lengths and mismatched type tags. This differs from the native field `from_bytes` operation, which reduces modulo the field order.

## Scope

[ForeignTransport.lean](../../tests/ForeignTransport.lean) selects between private values and typed constants, compares against public expectations, and returns all six types. The [native case](../../runtime/tests/foreign_transport.rs) uses boundary field values and generator points and checks both selection paths, exact private-field count, altered public/private transcripts, family mismatch and byte aliases. A focused Rust Session case checks the witness path.

[Field/group arithmetic and byte conversions](foreign-operations.md) and [foreign ledger state](foreign-trees.md) have separate checks. The native control runtime evaluates foreign values in helper plans. Proof generation, deployment, whole-language preservation and formal witness reconciliation remain in the wider qualification work. [Issue 21](https://github.com/awjreynolds/noctium/issues/21)
