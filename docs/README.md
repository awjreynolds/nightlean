# Nightlean documentation

Nightlean joins Lean contract authoring and proof development to Midnight's native proving and ledger interfaces. Start with the [repository quick start](../README.md#try-the-compiler) or the [architecture and assurance overview](designs/architecture.md).

## Choose a path

| Your task | Start here |
| --- | --- |
| Write and compile a contract | [Private claim source](../examples/PrivateClaim.lean), [bounded scalars](../examples/BoundedScalars.lean), [named helpers](development/named-helpers.md) |
| Understand private and public data | [Scalar disclosure](development/disclosure.md), [structured host control](development/structured-control.md), [private-state lifecycle](designs/private-state-lifecycle.md) |
| Embed native execution | [Rust runtime](development/native-rust-runtime.md), [C/C++ ABI](development/native-runtime-abi.md) |
| Build a native application | [Rust client](development/native-client.md), [proof API](development/native-proof-api.md), [native assembler](development/native-assembler.md) |
| Inspect or reproduce the proofs | [Source proofs](development/private-claim-proofs.md), [proof registration and kernel audit](development/proof-registration.md), [native proof chain](#follow-the-proof-chain) |
| Review scope and contribute | [Capability goal](compatibility/GOAL.md), [public issue map](https://github.com/awjreynolds/nightlean/issues/1), [contributing](../CONTRIBUTING.md) |

## Reproduce native evidence

The compiler-only quick start requires Git and the pinned Lean toolchain. Native qualification has a larger environment. Follow each guide's exact profile, source pins and prerequisites.

1. Build the [independent native ZKIR toolchain](development/native-toolchain.md).
2. Prepare [retained public bundles](development/portable-artifacts.md) and an [isolated localnet](../scripts/localnet/README.md).
3. Use the [Rust client and its qualification test](development/native-client.md), or the optional [JavaScript development harness](development/native-contract.md).
4. Compare the retained evidence for the [native claim](development/native-localnet.md), [bounded scalars](development/unsigned-localnet.md) and [selected 3.2.1 profile](development/zkir-3.2.1-integrated.md).

Keep private invocation files separate from public artifacts. Receipt reports identify their tested program, source revision and target profile. A passing example does not qualify the full capability inventory.

## Follow the proof chain

| Boundary | Evidence and reproduction |
| --- | --- |
| Actual source semantics | [Private-claim functional and source privacy proofs](development/private-claim-proofs.md) |
| Accepted theorem statements and dependencies | [Typed proof registration, model pins and fresh-kernel audit](development/proof-registration.md) |
| Source relation to native constraints | [Arbitrary-witness soundness and source completeness](development/private-claim-lowering-proofs.md) |
| Source transition to native VM and transcript | [State, framing, replay and public transcript preservation](development/private-claim-native-state-proofs.md) |
| Source privacy to native observations | [Successful-run native privacy and its excluded observables](development/private-claim-native-privacy-proofs.md) |
| Exact bytes and build provenance | [Qualified immutable builds and exact retained-byte certificates](development/private-claim-artifact-certificates.md), with functional/privacy composition |
| Deployed identity | Open [key/deployment binding](https://github.com/awjreynolds/nightlean/issues/57) |
| Generic compiler preservation | Open [scalar compiler proof work](https://github.com/awjreynolds/nightlean/issues/64), followed by broader feature coverage |

The [assurance report](development/assurance.md) documents the proved pruning pass and external boundaries. The [proof audit chain research](research/lean-proof-audit-chain.md) explains the required release chain. Claim-specific proofs do not establish correctness for every source program.

## Language and capability references

- [Scalar design](designs/scalar-types.md), [native unsigned lowering](development/native-unsigned-scalars.md) and [producer safety gate](development/native-producer-safety.md).
- [Composite type identity and bounded layouts](development/composite-types.md), plus [checked values and Rust/C++ codecs](development/composite-values.md). Aggregate source effects still need component disclosure integration.
- [Portable runtime design](designs/portable-runtime.md) and the [host/runtime boundary](research/nightlean-portable-runtime-boundary.md).
- [ZKIR capability research](research/zkir-v3-full-coverage.md), [native inventory](compatibility/zkir-feature-matrix.json) and [ledger capability research](research/midnight-ledger9-capabilities.md).
- [Compact comparison baseline](research/compact-equivalence-baseline.md). Inventory entries are not a completion percentage.
- [Glossary](../GLOSSARY.md) for the distinctions between circuits, Impact execution, target profiles and ledger state.

Older spike and packaging reports preserve historical evidence. Use the current native client and selected-profile guides for new integration work.

## Project visual

[Download the 1200 × 630 PNG](assets/nightlean-social.png) for LinkedIn or X/Twitter, or use the [editable SVG](assets/nightlean-social.svg). The card describes a research preview and separates published evidence from open assurance work. Both assets use the repository's [MIT license](../LICENSE).
