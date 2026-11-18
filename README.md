<p align="center">
  <img src="docs/assets/noctium-social.png" alt="Noctium research preview. Prove contract behavior in Lean and compile for Midnight. Published evidence covers the private claim's correctness, scoped privacy and exact artifacts. Native state examples include guarded effects, nested maps, records and Bytes32 SHA-256 account hashes. The historical selected claim has deployed verifier binding. Generic scalar lowering has soundness and source-completeness proofs. Frontend, broader circuit and ledger preservation remain open." width="100%">
</p>

<p align="center">
  <a href="#try-the-compiler">Quick start</a> ·
  <a href="docs/README.md">Documentation</a> ·
  <a href="docs/assets/noctium-capabilities.png">Capability goals</a> ·
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

The output includes the standalone `boundedRelation.zkir`, contract-call `BoundedScalars.apply.zkir`, runtime plan `BoundedScalars.apply.impact.json`, and `noctium.json` manifest. This compiler workflow needs no Rust, Node or running chain. Compile trusted Lean source: imports and elaborators execute development code.

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

SDK goals cover native Rust/C/C++, TypeScript with WASM for web dapps, Kotlin for Android and Swift for iOS. Rust and C/C++ retain historical qualified private-claim and [typed source-witness](docs/development/typed-witness-qualification.md) proof, transaction and private-state evidence on localnet. Web/mobile packages and full witness-language coverage remain goals.

Today: `Native`, `Bool`, bounded unsigned scalars, typed helpers, [bounded type and natural specialization](docs/development/generics.md), scalar and component disclosure checks, and lazy host control. Checked composite layouts and codecs are present. [Source helper outputs](docs/development/component-disclosure.md) flatten checked composite results into native circuit leaves. Source/native examples cover guarded state effects, Bytes32 map keys, [nested owner/spender paths](tests/NestedEscrow.lean), Native-field records, [native Counter operations](docs/development/native-counter.md), [memo Lists](docs/development/native-lists.md), account hashes and domain-separated SHA-256 preimages.

Typed Jubjub operations support a [derived-key, ElGamal and ECDH memo example](tests/Issue70DerivedCrypto.lean). [Field inversion](tests/NativeInverse.lean) supports Native and JubjubScalar, including zero rejection and safe inactive guards. [Typed byte conversions](tests/NativeByteConversions.lean) cover Native, JubjubScalar and JubjubPoint with modular field decoding and strict canonical point decoding. This is native-checker evidence, with no new proof or deployment. [Byte indexing](tests/NativeByteIndexing.lean) covers raw and computed Bytes32 values.

[Typed curve callbacks](tests/CurveWitness.lean) also pass Jubjub scalars and points through the Rust witness runtime into native constraints without Node. An [ElGamal witness contract](tests/CurveHelpers.lean) checks key ownership and decryption, then releases four computed ciphertext coordinates. A [private wallet example](tests/HashWitness.lean) now derives account IDs, encryption keys and ECDH memos from Bytes32 secrets and a private seed callback. [Typed getter results](docs/development/committed-returns.md), including Bytes32 and Jubjub values, now bind post-effect values to Midnight’s output commitment. Mixed ledger values, remaining cryptography, other return layouts and broader composition remain open. Explore the [full capability goals graphic](docs/assets/noctium-capabilities.png).

A [confidential-token milestone](docs/development/confidential-token.md) now combines registration, pending mint, authenticated sweep, transfer, burn, self-moves, epoch-checked memo clearing and checked views in one source module. Its focused native lifecycle checks two wallets, encrypted balances, supply, memos and counters. This covers twelve of sixteen reference entrypoints, with no new proof or deployment.

Start with the [public issue map](https://github.com/awjreynolds/noctium/issues/1) and [contribution guide](CONTRIBUTING.md). The [documentation index](docs/README.md) connects authoring, runtime integration, proof reproduction and capability research.

[MIT license](LICENSE) · [Security reporting](SECURITY.md) · [Shareable project card](docs/README.md#project-visual)
