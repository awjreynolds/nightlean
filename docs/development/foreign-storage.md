# Secp cells and map values

All six Secp256k1/Secp256r1 Base, Scalar and Point types support direct scalar cells and scalar map values. Map keys retain their existing Native or Bytes32 representation. [Nested scalar tree leaves](foreign-trees.md) share these encodings. Foreign map keys and record leaves need separate qualification.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit setKey where
  private key : Secp256k1Point
end

noctium_contract KeyRegistry where
  cell storedKey : Secp256k1Point
  entry update uses setKey where
    write storedKey := disclose(key)
    read storedKey as currentKey
    return saved : Secp256k1Point := disclose(currentKey)
  end
end
```

Ledger cells are public. A private witness value needs explicit `disclose` before a write, including a foreign point. Storing a point does not hide its coordinates.

## Representation and defaults

The compiler and Rust runtime use the same native encoding. Base and Scalar occupy two adjacent Field atoms. Point occupies five. Plan schemas retain the logical source type, so decoding checks both the exact width and canonical native representation. No custom ledger alignment or byte wrapper is involved.

Default fields are zero and default points are identity. Their encoded Field atoms are not an all-zero array. Constructor initialization and inactive guarded reads preserve those logical defaults. A guarded read of an absent map entry returns the default only when its guard is false. An active read still requires a present, valid value.

## Focused evidence

[ForeignStorage.lean](../../tests/ForeignStorage.lean) exercises both families and all roles in six cells and six maps. The [native checker case](../../runtime/tests/foreign_storage.rs) checks constructor defaults, old values, write/read results, overwrite behavior, missing guarded map reads and sibling preservation across two invocations. It also rejects altered public transcript data, malformed stored widths, out-of-range limbs, invalid point encoding and foreign map-key schemas.

These checks execute the native ledger state machinery and upstream circuit checker. They add no proving keys, proofs or chain deployment. Formal preservation and the remaining storage shapes stay under the [full native goal](../compatibility/GOAL.md).
