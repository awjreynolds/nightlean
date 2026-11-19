<p align="center">
  <img src="docs/assets/noctium-pitch.png" alt="Noctium research preview. Lean 4 contracts and checked specifications compile directly to native Midnight artifacts. Scoped support covers all 40 non-deprecated native instruction names and 15 native type families. Native Rust and C/C++ SDKs, typed helpers, modules, generics, composite values, guarded control and witnesses are implemented. Full native coverage, contract composition and web/mobile SDKs remain goals." width="100%">
</p>

<p align="center">
  <a href="#try-the-compiler">Quick start</a> ·
  <a href="docs/README.md">Documentation</a> ·
  <a href="docs/assets/noctium-pitch.png">Project pitch</a> ·
  <a href="docs/designs/architecture.md">Architecture &amp; assurance</a> ·
  <a href="https://github.com/awjreynolds/noctium/issues/1">Roadmap</a>
</p>

<p align="center">
  <a href="https://github.com/awjreynolds/noctium/actions/workflows/ci.yml"><img src="https://github.com/awjreynolds/noctium/actions/workflows/ci.yml/badge.svg" alt="POC compiler checks CI"></a>
</p>

Noctium is a Lean 4 compiler and proof framework for Midnight private contracts. Define the behavior your contract must satisfy, prove those properties against the actual source, and compile directly to Midnight's native formats.

- **Write** circuit constraints and ledger transitions in a typed Lean DSL.
- **Specify and prove** correctness, invariants and scoped privacy with ordinary Lean theorems and tactics.
- **Compile and execute** through native ZKIR circuits, Impact ledger plans and a Rust client for proving, funding, submission and recovery.

The compiler and primary lowering are written in Lean. Contract execution uses a finite supported subset. Proof authoring uses Lean's full theorem language. The Rust and C/C++ application paths need no Node, and Noctium has no Compact compiler or runtime dependency.

The Rust host uses Midnight's pinned on-chain runtime to prepare native Impact ledger operations, reads, costs and transaction transcripts. The node verifies the proof and executes those ledger operations against chain state. Witness execution and persisted private state stay off chain.

A private circuit input supplies a witness value for one call. Persisted private state lives in the application's wallet, and ledger cells and maps are public. Using a secret in arithmetic does not publish the result. `disclose(result)` authorizes public release, while an accepted proof also reveals its declared predicate. The [private state counter](examples/PrivateStateCounter.lean) shows readable private reads, typed callbacks, `prove` conditions and staged updates. See the [example guide](examples/README.md) and [privacy authoring review](docs/research/human-readable-privacy-authoring.md) for the boundaries and Compact's bounds.

**Research preview.** The private-claim example has source correctness, native preservation and scoped privacy proofs, joined to exact retained artifacts by byte/build certificates. Retained byte and deployment receipts qualify their recorded historical commits. They do not qualify the renamed source tree. These are claim-specific guarantees. Native state examples include guarded effects, nested maps, records and Bytes32 SHA-256 account hashes. The historical selected claim has deployed verifier binding. Generic scalar lowering has soundness and source-completeness proofs. Frontend, broader circuit and ledger preservation remain open. See [what is proved and what is trusted](docs/designs/architecture.md#assurance-boundaries).

## Try the compiler

Install [elan](https://github.com/leanprover/elan#installation) and Git. Elan selects the repository's pinned Lean **4.35.0** toolchain. Run:

```sh
git clone https://github.com/awjreynolds/noctium.git
cd noctium
lake build
lake exe noctium check examples/BoundedScalars.lean
lake exe noctium compile examples/BoundedScalars.lean --output build/bounded
```

The output includes the standalone `boundedRelation.zkir`, contract-call `BoundedScalars.apply.zkir`, runtime plan `BoundedScalars.apply.impact.json`, and `noctium.json` manifest. Use a new or empty output directory for each compile. The CLI publishes the complete directory after Lean succeeds. This compiler workflow needs no Rust, Node or running chain. Compile trusted Lean source because imports and elaborators execute development code.

For packaging a contract, `--emit ledger --emit witness` selects the ledger relations, Impact plans and their witness artifacts. Add `--bindings rust` for typed Rust witness modules. See [compiler output roles](docs/development/portable-artifacts.md#select-compiler-outputs).

Add `--dedup-range-checks` to remove a range check when an earlier check bounds the same circuit value to an equal or narrower width. Generate fresh keys for any relation the pass changes. [OpenZeppelin measurements](docs/development/oz-compile-performance.md#exact-range-check-deduplication)

For native proofs and transactions, follow the [Rust client guide](docs/development/native-client.md) or [C/C++ client ABI](docs/development/native-client-abi.md), [retained artifact workflow](docs/development/portable-artifacts.md) and [pinned native toolchain setup](docs/development/native-toolchain.md). Those paths add Rust, native build tools, proving parameters and an isolated localnet. The [JavaScript development harness](docs/development/native-contract.md) is an optional reproducibility path.

Use `Noctium.Frontend`, the `Noctium` scope and `noctium_*` declarations. Native hosts use `noctium_*` C symbols and `noctium_*.h` headers. The compiler and runtime now use one [canonical namespace](docs/development/namespaces.md).

## A small, real example

This circuit from [`examples/BoundedScalars.lean`](examples/BoundedScalars.lean) constrains the sum of two private 8-bit values to a public result:

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit boundedRelation where
  public expected : UIntRange 511
  private left : UInt 8
  private right : UInt 8
  let sum : UIntRange 511 := add(left, right)
  assert eq(sum, expected)
  output result : UIntRange 511 := expected
end
```

The full example writes the result to a ledger cell. The current [private claim example](examples/NoctiumPrivateClaim.lean) adds private witness calculations, explicit root/nullifier release and a public replay-prevention map. The separate [historical qualified source](examples/PrivateClaim.lean) stays byte-pinned for its [actual-source proofs](docs/development/private-claim-proofs.md). The teaching copy has no inherited proof receipts. See the [example guide](examples/README.md) for the private-input and private-state distinction.

## What is proved

Lean theorems establish specified contract properties. Runtime zero-knowledge proofs establish satisfaction of the emitted circuit and bound statement. The preservation proofs and artifact certificates below connect source properties to native artifacts for the qualified private claim.

| Published result | What the evidence establishes |
| --- | --- |
| [Source behavior](docs/development/private-claim-proofs.md) | Eligibility equations, exact state updates, invariants, framing and replay rejection. Six source mutations invalidate their expected proof clauses. |
| [Proof audit](docs/development/proof-registration.md) | Exact theorem/model checks, fresh-kernel replay and transitive axiom checks. Functional and privacy obligations stay separate. |
| [Native relation](docs/development/private-claim-lowering-proofs.md) and [state](docs/development/private-claim-native-state-proofs.md) | Claim-specific soundness for arbitrary satisfying assignments and checked VM traces, source completeness and transcript preservation. |
| [Scoped privacy](docs/development/private-claim-native-privacy-proofs.md) | Equal public native observations for successful claim executions under explicit assumptions. Proof bytes, failures, logs and timing are excluded. |
| [Exact artifacts](docs/development/private-claim-artifact-certificates.md) | Independent immutable-source builds and kernel checks bind the claim's functional/privacy proofs to retained raw bytes. |
| [Deployed claim identity](docs/development/private-claim-deployment-audit.md) | Public-only auditing joins the pinned source certificate, native key generation, initialized state and finalized operation under explicit trusted-node assumptions. |
| [Generic scalar lowering](docs/research/generic-scalar-preservation.md) | Soundness and source completeness for the actual scalar lowerer, with arbitrary native witnesses, explicit typed input/hash premises and independently pinned two-role kernel auditing. |
| [Native integration tests](docs/development/native-client.md#retained-qualification) | Real ZK proofs, funded transactions, finalized state checks and recovery on both 3.2.0 and 3.2.1 profiles. [Bounded scalar tests](docs/development/unsigned-localnet.md) add 34 adversarial witness cases. |

Native cryptography, parser/VM agreement, host behavior and authenticated authority inputs remain [trusted boundaries](docs/designs/architecture.md#assurance-boundaries). Localnet receipts provide integration evidence. They do not establish generic compiler correctness or production readiness.

## Direction and contributions

The destination is [full native ZKIR v3 and Midnight ledger capability coverage](docs/compatibility/GOAL.md). Compact feature equivalence is a minimum comparison, not the scope limit.

Rust, C/C++, Swift and Kotlin Android have localnet evidence for the original private claim and [typed source-witness](docs/development/typed-witness-qualification.md) workflows. The [Swift SDK](docs/development/swift-witness-sdk.md) generated local proofs, finalized calls, and recovered and committed private state on Apple Silicon macOS and the iOS simulator. The [Kotlin Android SDK](docs/development/android-witness-sdk.md) proved and finalized both workloads on an arm64 emulator and recovered private state for the typed witness. The [TypeScript/WASM SDK](docs/development/web-witness-sdk.md) authenticates the bundle, executes the Lean witness and generates and verifies the K7 typed-witness call proof in Chrome. Physical-device qualification, browser transactions and browser recovery remain goals.

Today: `Native`, `Bool`, bounded unsigned scalars, typed helpers, [bounded type and natural specialization](docs/development/generics.md), scalar and component disclosure checks, and lazy host control. Checked composite layouts and codecs are present. [Source helper outputs](docs/development/component-disclosure.md) flatten checked composite results into native circuit leaves. Source/native examples cover guarded state effects, Bytes32 map keys, [nested owner/spender paths](tests/NestedEscrow.lean), Native-field records, [guarded map deletion](docs/development/native-map-remove.md), [native Counter operations](docs/development/native-counter.md), [memo Lists](docs/development/native-lists.md), account hashes and domain-separated SHA-256 preimages.

Typed Jubjub operations support a [derived-key, ElGamal and ECDH memo example](tests/Issue70DerivedCrypto.lean). [Field inversion](tests/NativeInverse.lean) supports Native and JubjubScalar, including zero rejection and safe inactive guards. [Typed byte conversions](tests/NativeByteConversions.lean) cover Native, JubjubScalar and JubjubPoint with modular field decoding and strict canonical point decoding. This is native-checker evidence, with a [source constructor and sealed metadata](docs/development/constructors.md). Nominal ABI work remains open. These focused primitive checks are separate from the token proof/deployment evidence below. [Byte indexing](tests/NativeByteIndexing.lean) covers raw and computed Bytes32 values. [Byte reversal](tests/NativeByteReverse.lean) emits modern ZKIR `reverse`, preserves private origins and has a Lean reverse-twice theorem plus a focused native checker case.

[Fixed byte values](docs/development/fixed-bytes.md) add `Bytes n` up to 1024 bytes, with reversal, slicing, concatenation, equality and typed results. The source and native checker cases cover field-chunk boundaries and empty-value checks. Existing Bytes32 encodings stay compatible.

[SHA-512 and Keccak-256](docs/development/byte-hashes.md) compile directly from bounded byte preimages, including empty inputs. Their typed digests compose with byte operators, and private origins still require explicit disclosure. Focused source, native-checker, circuit-sizing and host-interpreter cases pass.

[Typed Boolean gates](docs/development/boolean-gates.md) add eager `boolAnd`, `boolOr` and `boolXor`, with explicit native Bool bridges. Both operands retain their assertions, and private results still require disclosure.

[Explicit typed copy](docs/development/native-copy.md) completes registration of all 40 non-deprecated opcode names in the pinned ZKIR inventory. The seven deprecated names remain unexposed. The opcode count measures scoped source support.

[Hash-to-curve](docs/development/hash-to-curve.md) maps ordered Native fields to a typed Jubjub point, including empty input. Results compose with point arithmetic and byte encoding. Application domain fields stay explicit.

[Typed Secp transport](docs/development/foreign-transport.md) adds public/private inputs, canonical literals, equality, selection and results for both Secp256k1 and Secp256r1 Base/Scalar/Point types. [Field/group operations](docs/development/foreign-operations.md) add arithmetic, point multiplication, coordinates and typed byte conversions, with retained active failures and safe inactive guards. [Scalar storage](docs/development/foreign-storage.md) adds six typed cells and map values with canonical decoding and guarded defaults. [Nested ledger trees](docs/development/foreign-trees.md) extend scalar leaves to all nine foreign types, with explicit parent creation, canonical defaults and sibling preservation.

[Curve25519](docs/development/curve25519.md) adds typed Base, Scalar and prime-order Edwards Point values, native operations and byte conversions, with four-field point storage. Lean subgroup checks and native vectors cover the distinct scalar encoding and identity rules.

[Jubjub storage](docs/development/jubjub-storage.md) adds checked scalar and point cells, map values and nested leaves. Missing guarded reads produce zero or identity before native reconstruction.

[Packed public Bytes32](docs/development/public-bytes32.md) reduces each public byte-input prologue from 64 VM operations to two. The retained and packed artifacts produce the same native-checked state, with private byte inputs unchanged.

[Byte ledger values](docs/development/byte-storage.md) retain exact lengths from zero through 1024 in cells, map values and nested leaves. Empty byte cells remain distinct from missing state. Private values require explicit disclosure before storage.

[Scalar byte decoding](docs/development/scalar-from-bytes.md) reduces up to 1024 little-endian bytes directly into Native or JubjubScalar. Empty operands retain their assertions, and the existing 32-byte and point decoders stay compatible.

[Ordered transient hashing](docs/development/transient-hash.md) hashes raw Native field vectors without inserted serialization fields. Empty vectors and legacy Poseidon2 compatibility have focused native checks. Cached results retain operand assertions.

[Typed signature helpers](docs/development/signatures.md) expose secp256k1/P-256 ECDSA, Jubjub Schnorr, Ed25519 and Ethereum address derivation through Lean and existing native operations. Private verification results require explicit disclosure. Protocol bounds and abort-versus-false behavior are documented.

The recipient-bound disclosure example binds ciphertext to a sealed Jubjub key. Lean proves the source policy, and the intended recipient recovered the bounded value from a finalized K12 call on localnet. [Directed disclosure example](docs/development/directed-disclosure.md)

[Native helper branches](docs/development/native-helper-branches.md) compile witness-free structured control and lazy expressions into existing native constraints. Focused checks cover inactive failures, lexical scope, aggregate sequencing and a guarded cell update. The separate [structured state entry](docs/development/structured-cells.md) route lowers typed cell and map reads, membership queries and writes inside helper bodies. Typed providers now receive ordered native state reads through `WitnessExecution`, with a focused cell update and private-staging case. Aggregate state bodies and complete guarded proof/ledger qualification remain open.

[Resumable native preparation](docs/development/native-preparation-cursor.md) exposes ledger reads before later private inputs arrive. The current Rust case computes a private input from the checked state read, resumes the same native executor and checks the resulting state. Integration with source witness/state scheduling remains open.

[Guarded typed witnesses](docs/development/guarded-witnesses.md) bind conditional provider calls to native slots, skip inactive callbacks and enforce canonical inactive defaults. Shared continuations, unit and empty results retain exact call records. Straight-line bindings keep their existing format.

[Typed curve callbacks](tests/CurveWitness.lean) also pass Jubjub scalars and points through the Rust witness runtime into native constraints without Node. An [ElGamal witness contract](tests/CurveHelpers.lean) checks key ownership and decryption, then releases four computed ciphertext coordinates. A [private wallet example](tests/HashWitness.lean) derives account IDs, encryption keys and ECDH memos from Bytes32 secrets and a private seed callback. [Committed results and typed call arguments](docs/development/committed-returns.md) bind typed values, including composite SDK views, to Midnight’s communication commitment. [Native call claims](docs/development/native-call-claims.md) assemble into ordered intents with checked identities and preimages. Two Rust owners also proved their own calls locally. Their coordinator attached the two proofs, and localnet finalized both calls in one extrinsic. [Separate-owner evidence](docs/development/independent-composition-receipt.json)

A [confidential-token milestone](docs/development/confidential-token.md) now combines registration, pending mint, authenticated sweep, transfer, burn, self-moves, epoch-checked memo clearing, encrypted escrow approval/replacement, delegated transfer/burn and checked views in one source module. Its Rust host completed 17 finalized localnet calls across all sixteen reference circuit entrypoints, using native proofs, source witness callbacks and committed private journals. The final checks cover two wallets, encrypted balances, supply, escrow, memos and counters. [Public receipts](tests/confidential-token-localnet-evidence.json)

On an Apple M3 Max, the CLI reduced the OpenZeppelin port's ledger-and-witness compile from 32.02 s to 6.01 s by loading the native Lean compiler library. All 53 output files matched byte for byte. These source timings exclude keys and proofs. [Compiler benchmark and Compact comparison](docs/development/oz-compile-performance.md#precompiled-lean-frontend)

Start with the [public issue map](https://github.com/awjreynolds/noctium/issues/1) and [contribution guide](CONTRIBUTING.md). The [documentation index](docs/README.md) connects authoring, runtime integration, proof reproduction and capability research.

[MIT license](LICENSE) · [Security reporting](SECURITY.md) · [Shareable project card](docs/README.md#project-visual)
