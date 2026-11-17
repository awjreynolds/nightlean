# Ledger 9 ZKIR capability matrix

Context pointer: [ticket 14, Audit source-level ZKIR and ledger capabilities beyond Compact](https://github.com/awjreynolds/noctium/issues/14)

Research checked on 2026-11-16 against pinned Midnight sources and release notes. This is a source audit, not a compile, proof, or deployment test.

## Pins and version boundary

| Layer | Version or source pin | Evidence |
| --- | --- | --- |
| Public ledger profile | Ledger 9.1.0.1, release commit `a2b3012` | [Ledger 9.1.0.1 release](https://github.com/midnightntwrk/midnight-ledger/releases/tag/ledger-9.1.0.1) |
| Ledger build dependencies | `midnight-zkir` 3.2.0, `midnight-circuits` 7.3.0, `midnight-zk-stdlib` 2.4.0 | The release labels these “build pins, not QA-verified.” |
| ZKIR source | Tag `zkir-3.2.0`, commit `446c7fecc6bd41dab99ebe89ab404e9d077d11a9` | [Release notes](https://github.com/midnightntwrk/midnight-zkir/blob/446c7fecc6bd41dab99ebe89ab404e9d077d11a9/.github/release-notes/zkir-3.2.0.md) |
| Compact path | Compact toolchain 0.36.0, language 0.28.0, Compact runtime 0.21.0 | [Compact 0.36.0 notes](https://docs.midnight.network/relnotes/compact/toolchain-0.36.0) |
| On-chain runtime | Ledger 9 runtime v4 line, crate 4.0.1 in the 9.1.0.1 release artifacts | [Ledger artifacts](https://github.com/midnightntwrk/midnight-ledger/releases/tag/ledger-9.1.0.1) |

These identifiers do not describe one interchangeable format. Compact 0.36 says it emits ZKIR 3.1 while bundling a `zkir-v3` binary from `midnight-zkir` 3.2.0-rc.2. Ledger 9.1.0.1 pins final ZKIR 3.2.0. The exact producer output and target acceptance still need a pinned artifact check.

## Source-level surface at ZKIR 3.2.0

The Rust implementation defines 15 value types: native field, boolean, byte, variable-length bytes, Jubjub point/scalar, and point/base/scalar types for Secp256k1, Secp256r1, and Curve25519. Its `Instruction` enum has 47 variants, including older variants retained for compatibility.

The 47 source variants are grouped below. Seven are retained deprecated ZKIR 3.0 compatibility instructions.

- Inputs, outputs, and constraints: `PublicInput`, `PrivateInput`, `Impact`, `Output`, `Encode`, `Assert`, `ConstrainBits`, `ConstrainEq`, `ConstrainToBoolean`, and `CondSelect`.
- Values and arithmetic: `Copy`, `LoadConstant`, `Add`, `Mul`, `Neg`, `Inv`, `TestEq`, `LessThan`, `Not`, `And`, `Or`, and `Xor`.
- Curves: `EcMul`, `EcMulGenerator`, `HashToCurve`, `IntoCoordinates`, `FromCoordinates`, and `JubjubScalarFromNative`.
- Bytes and hashing: `IntoBytes32`, `FromBytes32`, `ReverseBytes`, `Bytes32IntoLowHigh`, `Bytes32FromLowHigh`, `DivModPowerOfTwo`, `ReconstituteField`, `TransientHash`, `PersistentHash`, `Keccak256`, `Slice`, `Nth`, `Concat`, `Sha512`, `ToBytes`, `FromBytes`, `Reverse`, `BytesIntoNatives`, and `BytesFromNatives`.
- Compatibility operations: the source retains seven deprecated ZKIR 3.0 instructions for older circuits. New compiler output should prefer their documented replacements where one exists.

The pinned source is the [instruction/type implementation](https://github.com/midnightntwrk/midnight-zkir/blob/446c7fecc6bd41dab99ebe89ab404e9d077d11a9/zkir/src/ir.rs) and [type definitions](https://github.com/midnightntwrk/midnight-zkir/blob/446c7fecc6bd41dab99ebe89ab404e9d077d11a9/zkir/src/ir_types.rs). The release notes describe the ZKIR 3.2 additions: Bool, Byte, Bytes(n), byte operations, boolean gates, constants, SHA-512, and typed byte conversions for fields and curve points.

ZKIR is a straight-line circuit relation format. It does not define a contract language or ledger state machine. The circuit source contains inputs, outputs, and instructions. Contract calls, state effects, transcript acceptance, and deployment metadata sit at other layers.

## Evidence matrix

| Capability | Present in pinned source | Ledger 9 acceptance evidence | Compact exposure | Complete direct contract/Preview path |
| --- | --- | --- | --- | --- |
| ZKIR v3 circuit formats and PLONK key generation | Yes. The repository defines the IR, VM, checker, prover, and compile tools. | Ledger release pins ZKIR 3.2.0 and describes v3 proofs and verifier keys. It does not publish an operation-by-operation verifier support matrix. | Yes, Compact 0.36 generates ZKIR v3, specifically format 3.1. | Not established. ZKIR tools compile circuit files into keys, but reviewed docs do not show a complete non-Compact bundle and transaction path. |
| Typed field, byte, and curve operations | Yes. Fifteen types and 47 instruction variants in the pinned Rust source. | Ledger pins the ZKIR and circuit library builds. This proves the component versions in the build, not that every source operation has a supported public authoring or deployment route. | Partial public evidence. Compact 0.36 documents SHA-512, Secp256r1/P256, Curve25519, and associated verification features. Its release notes do not map the full ZKIR operation set to source constructs. | Not established per operation. |
| Private/public circuit inputs and outputs | Yes. The ZKIR source models public and private transcript reads and typed outputs. | Ledger 9.1.0.1 documents versioned proofs, public-input accounting, call transcripts, and stricter transcript validation. Binding an arbitrary non-Compact schema to those structures is unverified. | Yes, through Compact witness declarations and its documented proof flow. | Not established. |
| Conditional public inputs (`Impact`) | Yes, as a ZKIR instruction. Its code describes guarded Native public inputs and activity data. | Ledger release notes establish transcript and public-input validation, not a standalone public compiler interface for this operation. | Mapping to a Compact source capability is unknown from reviewed release notes. | Not established. |
| Contract state, events, and cross-contract calls | Not part of the ZKIR instruction set. | Ledger 9 and the v4 on-chain runtime execute calls and validate state transcripts. | Compact 0.36 release notes document cross-contract behavior and ledger 9 notes list events and calls on the Compact path. | No reviewed source documents the complete direct-ZKIR binding and generated contract package for Noctium. |

“Present in source” means the pinned repository contains the implementation. “Ledger acceptance” means there is evidence for that capability at a layer relevant to transaction verification. These are separate claims. Library code, ZKIR parser support, a prover API, and a ledger-accepted contract call do not imply one another without integration evidence.

## What the comparison establishes

Compact 0.36 is one producer for this stack, not a description of every source-level ZKIR or ledger capability. Its release notes establish a subset of features, and say its compiler emits 3.1 while its bundled binary comes from a 3.2.0 pre-release. The ZKIR 3.2 release notes document additional types and operations in the implementation. They also say the minor version is a label and no instruction is gated by it. The version difference alone therefore does not prove those operations are unavailable from Compact. The notes do not provide a complete Compact-to-ZKIR mapping.

This audit did not confirm a specific feature that the ledger supports but Compact cannot express. It also did not prove Compact covers all ledger or prover capabilities. The evidence supports leaving the question open and building an explicit capability matrix from source and integration tests before committing Noctium to any broader feature list.

## Specification status

The ZKIR 3.2 source tree contains an Agda formalization and a language specification. The checked-in specification identifies itself as a working draft pinned to an earlier ZKIR 3.0.0 snapshot. It explicitly says its formalization does not yet cover later types and instructions. Treat the Rust source at the pinned release as the current implementation reference; do not claim formalized guarantees for the newer operation batch from that older specification.

- [Pinned ZKIR spec](https://github.com/midnightntwrk/midnight-zkir/blob/446c7fecc6bd41dab99ebe89ab404e9d077d11a9/zkir-spec/docs/zkir-v3-spec.md)
- [Pinned Agda formalization README](https://github.com/midnightntwrk/midnight-zkir/blob/446c7fecc6bd41dab99ebe89ab404e9d077d11a9/zkir-spec/src/zkir-v3/README.md)

## Recommendation

Keep Noctium's source semantics and compiler implementation in Lean. Model circuit relations, witness/public-input boundaries, typed outputs, contract state effects, and transaction bindings as separate parts of an extensible compiler representation. Keep the ledger/ZKIR/proving target profile versioned independently from the source model.

Use this report as a capability audit starting point, not a feature promise. For each proposed feature, record four facts: the implementation source, the relevant ledger/prover acceptance boundary, whether Compact exposes it, and a tested end-to-end artifact path. Add support tickets for confirmed ledger-backed capabilities after the source comparison and first vertical slice. Do not use Compact's feature list to exclude a lower-level capability, and do not use low-level source presence alone to promise deployability.

## Unresolved

- Which ZKIR 3.2 instruction variants have an end-to-end contract call and Preview acceptance path on the pinned public ledger stack?
- Which operations does Compact 0.36 emit in real generated ZKIR, versus operations the 3.2 checker/prover accepts but the compiler does not currently emit?
- Is there a stable language-independent API for building the witness schema, public statement, transcript binding, contract artifacts, and call metadata?
- Which capabilities in ledger and prover source are absent from Compact's source language, rather than simply undocumented in the reviewed release notes?
- Which of those candidates should enter Noctium's post-v1 support set after a compatibility spike?

These questions become source-level and integration work in the Noctium backlog. The private one-time claim is only the first program used to validate the compiler and runtime boundary.
