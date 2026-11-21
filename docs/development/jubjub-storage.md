# Jubjub scalar and point storage

JubjubScalar and JubjubPoint use the existing typed scalar storage path for direct cells, map values and nested ledger leaves. Keys retain their existing Native or Bytes32 types. Composite record leaves remain separate work.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit setPublicKey where
  private key : JubjubPoint
end

noctium_contract JubjubKeys where
  cell publicKey : JubjubPoint
  constructor() where
    initialize publicKey := jubjubFromCoordinates(0, 1)
  end
  entry replace uses setPublicKey where
    write publicKey := disclose(key)
    read publicKey as currentKey
    return saved : JubjubPoint := disclose(currentKey)
  end
end
```

Ledger values are public. A private witness point needs explicit disclosure before storage. This rule also applies to values derived from the witness.

## Canonical values and defaults

A scalar occupies one Native Field atom and must be below the Jubjub scalar order. A point occupies two Field atoms in x/y order. Runtime reads preserve the existing subgroup-checked point decoder and canonical coordinate round trip. An arbitrary on-curve point is not enough.

Scalar defaults are zero. Point defaults are identity, with coordinates `(0,1)`. Inactive guarded reads return those values without inspecting skipped state paths. Native reconstruction must use the identity coordinates before calling the point constructor, including the y-coordinate of one.

The compiler and runtime reuse the existing `pushFields` and `popeqFields` operations with logical Jubjub type tokens. This adds no opcode name or wire tag. Active reads check the declared leaf kind, encoded width, canonical value and alignment.

## Qualification

[JubjubStorage.lean](../../tests/JubjubStorage.lean) spans cells, maps and nested trees for both types. Its [native case](../../runtime/tests/jubjub_storage.rs) checks three invocations, all 12 old/new results, defaults, overwrite and sibling preservation. It rejects changed transcript data, wrong leaf roles, malformed widths, a modulus-sized scalar, an order-two point and unsupported Jubjub key schemas. The compiler build, source checks, guide snippet, native case and legacy runtime compilation pass. The existing foreign-tree case also passes after the shared codec change.

This scope is tracked in [issue 78](https://github.com/awjreynolds/noctium/issues/78). Runtime control parsing did not change, so this package adds no repeated witness Session campaign.

This storage slice covers source and native checking. [Byte ledger values](byte-storage.md) and [foreign keys](foreign-trees.md) have separate evidence. The [full native goal](../compatibility/GOAL.md) still includes composite leaves, proof and deployment evidence, and broader compiler preservation.
