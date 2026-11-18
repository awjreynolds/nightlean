# Noctium documentation

Write a contract, prove its specified behavior in Lean, and compile for Midnight. Start with the [compiler quick start](../README.md#try-the-compiler). To assess the guarantees, read [what is proved and what is trusted](designs/architecture.md#assurance-boundaries).

## Choose a path

| Your task | Start here |
| --- | --- |
| Write and compile a contract | [Current private claim example](../examples/NoctiumPrivateClaim.lean), [example guide](../examples/README.md), [bounded scalars](../examples/BoundedScalars.lean), [named helpers](development/named-helpers.md), [compile-time generics](development/generics.md) |
| Understand private and public data | [Scalar disclosure](development/disclosure.md), [structured host control](development/structured-control.md), [private-state lifecycle](designs/private-state-lifecycle.md) |
| Embed native execution | [Rust runtime](development/native-rust-runtime.md), [C/C++ ABI](development/native-runtime-abi.md) |
| Build a native application | [Rust client](development/native-client.md), [C/C++ client ABI](development/native-client-abi.md), [proof API](development/native-proof-api.md), [native assembler](development/native-assembler.md) |
| Review contract correctness | [Actual-source proofs](development/private-claim-proofs.md), [registered obligations and axiom policy](development/proof-registration.md) |
| Review compilation and trust | [Layered guarantees](designs/architecture.md#assurance-boundaries), [source-to-artifact proof chain](#follow-the-proof-chain) |
| Review scope and contribute | [Capability goal](compatibility/GOAL.md), [public issue map](https://github.com/awjreynolds/noctium/issues/1), [contributing](../CONTRIBUTING.md) |
| Follow the complex-contract POC | [OpenZeppelin token port and feature dependencies](development/openzeppelin-port.md) |

## Reproduce native evidence

The compiler-only quick start requires Git and the pinned Lean toolchain. Native qualification has a larger environment. Follow each guide's exact profile, source pins and prerequisites.

1. Build the [independent native ZKIR toolchain](development/native-toolchain.md).
2. Prepare [retained public bundles](development/portable-artifacts.md) and an [isolated localnet](../scripts/localnet/README.md).
3. Use the [Rust client and its qualification test](development/native-client.md), or the [C/C++ proof and transaction ABI](development/native-client-abi.md). Both have qualified private-claim deployment, call and recovery evidence on the two selected profiles. The [JavaScript development harness](development/native-contract.md) is optional.
4. Compare the retained evidence for the [native claim](development/native-localnet.md), [bounded scalars](development/unsigned-localnet.md) and [selected 3.2.1 profile](development/zkir-3.2.1-integrated.md).

Keep private invocation files separate from public artifacts. Receipt reports identify their tested program, source revision and target profile. A passing example does not qualify the full capability inventory.

## Follow the proof chain

These layers establish different properties. Contract theorems describe intended source behavior. Preservation and artifact certificates connect those properties to the qualified native claim. Runtime ZK proofs serve the separate role of proving an invocation satisfies its bound circuit statement.

| Boundary | Evidence and reproduction |
| --- | --- |
| Actual source semantics | [Private-claim functional and source privacy proofs](development/private-claim-proofs.md) |
| Accepted theorem statements and dependencies | [Typed proof registration, model pins and fresh-kernel audit](development/proof-registration.md) |
| Source relation to native constraints | [Arbitrary-witness soundness and source completeness](development/private-claim-lowering-proofs.md) |
| Source transition to native VM and transcript | [State, framing, replay and public transcript preservation](development/private-claim-native-state-proofs.md) |
| Source privacy to native observations | [Successful-run native privacy and its excluded observables](development/private-claim-native-privacy-proofs.md) |
| Exact bytes and build provenance | [Qualified immutable builds and exact retained-byte certificates](development/private-claim-artifact-certificates.md), with functional/privacy composition |
| Deployed claim identity | [Qualified source/key/deployment join](development/private-claim-deployment-audit.md), with public-only verification and explicit trusted-node assumptions |
| Generic scalar lowering | [Qualified soundness and source completeness](research/generic-scalar-preservation.md), exact two-role checks and independent model pin |
| Broader compiler preservation | Open [assurance work](https://github.com/awjreynolds/noctium/issues/21), including frontend, other native primitives and general ledger preservation |

The [assurance report](development/assurance.md) documents the proved pruning pass and external boundaries. The [proof audit chain research](research/lean-proof-audit-chain.md) explains the required release chain. Claim-specific proofs do not establish correctness for every source program.

## Language and capability references

- [Private/public state, witnesses and readable privacy authoring](research/human-readable-privacy-authoring.md), including Compact's bounds, current guarantees and proposed source syntax. The [example guide](../examples/README.md) separates current Noctium examples from historical qualified source.

- [Scalar design](designs/scalar-types.md), [native unsigned lowering](development/native-unsigned-scalars.md) and [producer safety gate](development/native-producer-safety.md).
- [Fixed byte values](development/fixed-bytes.md), including bounded lengths, reversal, slicing, concatenation, typed results and empty-value checks.
- [SHA-512 and Keccak-256](development/byte-hashes.md), with explicit preimages, private origins and direct native empty-input hashing.
- [Typed Boolean gates](development/boolean-gates.md), with eager operand checks, typed native bridges and preserved Boolean input encodings.
- [Hash-to-curve](development/hash-to-curve.md), from ordered Native fields to composable Jubjub points, including empty input.
- [Typed Secp transport](development/foreign-transport.md), public/private inputs, literals, equality, selection and results across six foreign types.
- [Secp arithmetic and bytes](development/foreign-operations.md), field/group operations, coordinates, canonical points, reducing field conversions and guarded partial operations.
- [Secp cells and map values](development/foreign-storage.md), canonical multi-field storage, constructor defaults and guarded reads.
- [Nested foreign ledger state](development/foreign-trees.md), typed scalar leaves, parent creation, guarded defaults and preserved sibling entries.
- [Curve25519 types](development/curve25519.md), prime-order Edwards points, distinct scalar encoding, typed operations and point storage.
- [Foreign-field implementation plan](designs/foreign-types.md), delivered Secp slices and remaining Curve25519, storage and assurance work.
- [Sequential native cell reads](development/sequential-state.md), with source-generated read-after-write fixtures on both runtime profiles. Generic state preservation remains separate proof work.
- [Composite type identity and bounded layouts](development/composite-types.md), plus [checked values and Rust/C++ codecs](development/composite-values.md). [Component-aware helper outputs](development/component-disclosure.md) compile to native circuit leaves with disclosure checks. Bytes32-keyed ledger records support nonempty Native-only layouts.
- [Portable runtime design](designs/portable-runtime.md) and the [host/runtime boundary](research/noctium-portable-runtime-boundary.md).
- [Typed source witnesses](development/typed-witnesses.md), including canonical composite calls, source-staged reads, public witness artifacts and the consuming native proof/client handoff.
- [ZKIR capability research](research/zkir-v3-full-coverage.md), [native inventory](compatibility/zkir-feature-matrix.json) and [ledger capability research](research/midnight-ledger9-capabilities.md). The [raw native guard experiment](research/native-guard-prerequisites.md) records verified prerequisites, with source guard support still gated.
- [Compact comparison baseline](research/compact-equivalence-baseline.md). Inventory entries are not a completion percentage.
- [Glossary](../GLOSSARY.md) for the distinctions between circuits, Impact execution, target profiles and ledger state.

Older spike and packaging reports preserve historical evidence. Use the current native client and selected-profile guides for new integration work.

The [Verity comparison](research/verity-lessons.md) records lessons for compiler proof structure, theorem scope and audit reporting, with immutable upstream sources.

## Project visual

The [1200 × 630 share card](assets/noctium-social.png) and [editable SVG](assets/noctium-social.svg) summarize the project goals. The [1600 × 1160 capability map](assets/noctium-capabilities.png) and [editable SVG](assets/noctium-capabilities.svg) show the full target feature set, including full pinned ZKIR v3 support and native, web and mobile SDKs. Both graphics label goals, published subset evidence and unfinished assurance separately. Assets use the repository's [MIT license](../LICENSE).
