# Canonical composite types and source layouts

`Nightlean.Types.Composite` defines the Lean-owned type/layout foundation for unit, scalar leaves, structural tuples, nominal structs, nominal enums, fixed vectors and fixed byte sequences. [Checked composite values](composite-values.md) adds construction, flattening, native relation constraints and a Rust/C++ value codec. Source aggregate effects and ledger acceptance remain separate work.

## Identity and ordering

Struct and enum declarations use qualified ASCII identities such as `Wallet.Note`. A repeated identity across either declaration kind rejects. Field and variant names must be unique within their declaration. Field order, variant order and tuple element order are significant. Nominal declarations compare by their declaration identity, even when their fields have identical layouts. Tuple and vector subtyping is structural and requires matching arity or length.

`CompositeSubtype` is a proof relation. It admits exact Native and Bool types, inclusive-maximum UInt widening only within the existing `ScalarPolicy.maxUint` bound, recursive tuple/vector relationships, exact fixed-byte lengths and exact nominal identities. It defines no implicit cast or physical-size-based conversion.

The full environment fingerprint sorts declaration records by canonical identity, then encodes fields and variants in source order. A type fingerprint encodes the type and its reachable declaration closure, so unrelated declarations do not perturb a specialization key. The versioned fingerprint is the full canonical descriptor string. It is not a cryptographic hash.

## Layout preflight

`CompositeEnv.validate` checks identities, duplicate names, unknown references, direct and indirect recursive layouts, scalar ranges, vector/byte bounds, expanded leaf counts and expanded node counts. It reports the declaration or referring field span. Forward references are allowed when acyclic. Fingerprint functions expect an environment which has passed this validation.

`checkedLayout` runs validation and bounded size preflight before constructing the finite inductive `Layout`. A `CheckedLayout` carries kernel-checked bounds for leaves, logical expanded values, and retained layout constructors. It proves equalities between all three preflight counts and recursive counts over the returned layout. `layout` returns the same checked layout value for callers which do not need the certificate fields. Fixed vector layouts keep one element layout, even at length zero. Preflight separately bounds logical value expansion and retained type-layout size, so zero-length nesting cannot multiply retained layout constructors without limit.

The local resource limits are 1,024 declarations, 1,024 elements or bytes per fixed sequence, 4,096 scalar leaves, 16,384 logical expanded nodes and 16,384 retained layout nodes. Callers can lower these limits for tests but cannot raise them above the published policy. These limits bound this compiler implementation. They do not claim a Compact or ZKIR language limit.

Zero-length vectors and byte sequences represent empty values in this source model and consume no scalar leaves. The pinned source-language and native artifact cases still need qualification before aggregate compilation is enabled.

## Scalar representation inventory

[`tests/composite-types/manifest.json`](../../tests/composite-types/manifest.json) records the current source layout leaves. Native, Bool and UInt each occupy one logical field slot; their respective canonicality/range constraints remain distinct. A byte occupies one UInt8-shaped field. An enum uses a checked UInt tag with maximum `variantCount - 1`, then a payload area sized to the largest variant. The proposed policy pads shorter variants with zero slots.

The enum tag and padding rules describe the source layout proposal. This package does not claim correspondence with the current native ledger ABI, ZKIR aggregate encoding or proof relation. Those rules need an explicit checked flattening transformation and native conformance evidence before Nightlean enables aggregate deployment.

## Bytes32 map-key slice

The selected ZKIR 3.2.1 path supports fixed-width `Bytes32` map keys with scalar map values. Circuit inputs expand to 32 ordered UInt8 leaves. Native map operations retain all 32 bytes under the pinned Bytes32 alignment and two-field encoding, and public byte inputs bind each leaf into the Impact transcript. `runtime/tests/fixtures/generic-state/issue69-bytes32/321` is generated from `tests/Issue69Bytes32Map.lean`. `runtime/tests/bytes32_map.rs` checks membership, guarded missing-key reads, insertion, scalar reads, and distinct byte strings whose scalar reductions would collide.

This slice does not enable byte arithmetic, equality, scalar casts, byte-valued state, circuit outputs, or direct byte witness bindings. `CompositeType.bytes` keeps its checked aggregate layout and codec. A scalar `.bytes` layout is rejected; a 32-byte composite layout retains 32 leaves.

## Nested Bytes32 scalar maps

The native ledger source surface now accepts recursive map state through `tree`, with typed bracket paths for membership, scalar reads and writes. `tests/Issue69NestedCounter.lean` models `_escrowSpendEpochs` as Bytes32 owner → Bytes32 spender → UInt64 count. It checks each parent with `member`, creates an absent owner map with explicit `insert ... := emptyMap`, inserts a missing scalar count, increments with checked UInt arithmetic and reads the result again. Empty-map assignment replaces the selected map entry, so callers must guard it with membership when they intend initialization. The fixed `tree` source declaration currently accepts two map levels and scalar leaves; the IR schema is recursive so later value kinds do not change legacy `StateKind.map`.

Native plans use `indexPath` for typed key paths. Empty-map creation indexes the parent with `pushPath`, pushes the final key and native map tag `2`, runs `new`, then `insert`. Scalar paths use aligned keys and the existing native `insert` update behavior. The focused source/native fixture lives under `runtime/tests/fixtures/generic-state/issue69-nested/321`; broader records, lists and Counter ADT semantics remain outside this slice.

## Cases and check

`tests/CompositeTypes.lean` contains the TYC-IDENTITY, TYC-ORDER, TYC-LENGTH, TYC-CYCLE and TYC-SUBTYPE cases. It checks insertion-order-stable fingerprints, field-order changes, nominal distinction, forward references, cycles, missing names, duplicate declarations, scalar bounds, sequence limits, enum tags/payloads and recursive UInt widening proofs. Its S8 nested zero-vector regression has three logical expanded nodes and 1,021 retained layout constructors. A 100-node retained-layout limit rejects it before layout construction. At a 1,021-node bound, the returned counts are `(expandedNodes, layoutNodes, value.expandedNodeCount, value.nodeCount) = (3, 1021, 3, 1021)`.

```sh
lake build Nightlean.Types.Composite
lake env lean tests/CompositeTypes.lean
```
