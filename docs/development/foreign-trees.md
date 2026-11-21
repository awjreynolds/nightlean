# Foreign values in nested ledger state

The ledger schema accepts Secp256k1, Secp256r1 and Curve25519 Base, Scalar and Point types as scalar leaves in nested maps. The ZKIR 3.2.1 target also accepts those types as keys in maps, sets and paths to nested collections. Composite record leaves need separate qualification.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit rememberKey where
  public owner : Native
  public application : Bytes32
  private key : Curve25519Point
end

noctium_contract NestedKeys where
  tree keys : Native => Bytes32 => Curve25519Point
  entry remember uses rememberKey where
    member keys[owner] as ownerPresent
    if eq(ownerPresent, false) then {
      insert keys[owner] := emptyMap
    } else {
    }
    insert keys[owner][application] := disclose(key)
    read keys[owner][application] as savedKey
    return saved : Curve25519Point := disclose(savedKey)
  end
end
```

Parent map creation stays explicit. A leaf read requires an existing value. Guard a read with membership when an entry might be absent. An inactive read supplies the canonical field zero or point identity without inspecting the skipped state path.

Ledger state is public. The example discloses the private witness key before storing the point. The public owner and application select the nested path.

## Shared encoding

Nested leaves use the same native encodings as [direct cells and map values](foreign-storage.md). Field values occupy two Field atoms. Curve25519 points occupy four, and Secp points occupy five. The Curve25519 Scalar low limb carries 204 bits. Runtime reads check the declared family and role, canonical encoding, width and exact alignment.

The compiler reuses existing `pushFields`, `popeqFields`, path indexing and insertion. This adds no wire tag or opcode name.

## Foreign keys

Declare a key's type in the ledger schema, for example `map balances : Secp256k1Base => UInt 64` or `tree claims : Native => Set Curve25519Point`. A lookup, insertion or removal uses the same declared type. The native runtime derives transcript width from the schema and uses the canonical sequence of Field atoms as the key. Base and Scalar keys use two atoms, Curve25519 points use four, and Secp points use five. A value of the wrong curve or role fails type checking even when its encoding has the same width.

Ledger keys are public. A key derived from a private witness requires explicit `disclose(...)` before any operation exposes the key on the ledger.

## Focused evidence

[ForeignTree.lean](../../tests/ForeignTree.lean) combines nested Curve25519 Scalar, Curve25519 Point and Secp256k1 Point leaves with Native and Bytes32 keys. The [native checker case](../../runtime/tests/foreign_tree.rs) creates parents, reads defaults, overwrites one key and inserts a second key while preserving the first. It checks all six typed results on each invocation and decodes the stored cells with the native codec.

The same case rejects changed public transcript data, malformed stored leaf width and a mismatched declared scalar role. [ForeignKeys.lean](../../tests/ForeignKeys.lean) and its [native checker case](../../runtime/tests/foreign_keys.rs) exercise two-, four- and five-field keys in maps, sets and nested paths. Three calls cover guarded reads, insertion, membership, removal and preservation of neighboring entries. The native runtime also reads Merkle paths beneath the two Secp point keys.

```sh
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
lake exe noctium compile tests/ForeignKeys.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/compiled"
NOCTIUM_FOREIGN_KEY_ARTIFACTS="$scratch/compiled" \
  cargo test --manifest-path runtime/Cargo.toml --locked --no-default-features \
  --features zkir-321 --test foreign_keys -- --ignored
```

These checks cover native state and circuit checking. Foreign record leaves, proving and deployment evidence for these shapes, and formal preservation stay under the [full native goal](../compatibility/GOAL.md).
