# Foreign values in nested ledger state

All nine Secp256k1, Secp256r1 and Curve25519 Base, Scalar and Point types work as scalar leaves in nested ledger maps. Keys retain the existing Native or Bytes32 types. Foreign keys and composite record leaves need separate qualification.

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

## Focused evidence

[ForeignTree.lean](../../tests/ForeignTree.lean) combines nested Curve25519 Scalar, Curve25519 Point and Secp256k1 Point leaves with Native and Bytes32 keys. The [native checker case](../../runtime/tests/foreign_tree.rs) creates parents, reads defaults, overwrites one key and inserts a second key while preserving the first. It checks all six typed results on each invocation and decodes the stored cells with the native codec.

The same case rejects changed public transcript data, malformed stored leaf width, a mismatched declared scalar role and a foreign map-key schema. These checks add no keys, proofs, deployment or repeated witness Session campaign. Runtime control parsing did not change. The remaining [full native goal](../compatibility/GOAL.md) includes foreign record leaves, foreign keys and broader preservation and integration assurance.
