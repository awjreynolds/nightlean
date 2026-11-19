# Scalar wire encoding

Use `serialize(value, width)` to produce a fixed-width byte string and `deserialize(Type, bytes)` to decode one inside a circuit or ledger entrypoint.

```lean
let count : UIntRange 301 := deserialize(UIntRange 301, countFrame)
output countWire : Bytes 4 := disclose(serialize(count, 4))
```

The type determines how many leading bytes decoding consumes. Serialization writes those bytes and appends zeros up to the requested width. Decoding ignores the remaining input bytes, matching Compact 0.36.1. The compiler checks both lengths. Private inputs keep their disclosure requirements through both operations. [Example](../../examples/ScalarSerialization.lean) · [Pinned reference implementation](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/analysis-passes/expand-serialize.ss)

| Value type | Encoding and checked decoding |
| --- | --- |
| `Bool` | One byte. Only 0 and 1 decode. |
| `UInt n`, `UIntRange n` | Little-endian. The declared inclusive maximum determines the width. A zero maximum uses zero bytes. Decoding checks the actual bound. |
| `Bytes n` | The first `n` bytes in source order. |
| `Native` | 32 little-endian bytes. The decoder compares the original prefix against the re-encoded residue to reject values at or above the field modulus. |
| `JubjubScalar` and foreign scalar or base fields | 32 little-endian bytes. Decoding reduces the input by the respective field modulus. |

The typed operations lower through the existing scalar and byte instructions. Event emission uses the same Boolean and unsigned byte encoders. The catalog circuit still measures K13 and 4,937 rows. Point encoding stays outside this interface. The codec also supports [readable witness helpers and typed aggregate helpers](aggregate-serialization.md). [Standard events](standard-events.md)

## Focused qualification

The pinned Compact 0.36.1 compiler and 0.21.0 runtime produced the reference values for Bool, bounded UInt, Bytes, Native, and a secp256k1 scalar. The Rust test checked the same five byte encodings, accepted foreign scalar reduction at the modulus, and rejected invalid Boolean, integer and Native frames. The pinned ZKIR checker rejected an altered private Native frame with the same residue and public result. Lean also rejected an undersized output, a point target, and an undisclosed private release.

Noctium compiled Jubjub scalar and zero-width cases. Compact 0.36.1 raised an internal compiler error for the attempted Jubjub reference circuit. Jubjub differential qualification remains open.

The authenticated native codec bundle used K11 and 1,483 rows on Ledger 9.1.0.1 and ZKIR 3.2.1.

| Isolated localnet action | Block | Transaction ID |
| --- | ---: | --- |
| Deploy | 31032 | `b6d8596a9765c59cd59c01e218bcdc088e0aba5d19328b79166cd85fb32bea88` |
| Call | 31035 | `2db288cb59fbb382cebd98cc1cceb86fca41796361a62d70137d0906027f88d3` |

```sh
lake build noctium
.lake/build/bin/noctium compile examples/ScalarSerialization.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/experiments/scalar-serialization
NOCTIUM_SERIALIZATION_ARTIFACTS="$PWD/build/experiments/scalar-serialization" \
  cargo test --manifest-path runtime/Cargo.toml --locked --no-default-features \
  --features zkir-321 --test scalar_serialization -- --ignored
```
