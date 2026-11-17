# Human-readable privacy authoring in Noctium

Research date: 2026-11-17. Read-only investigation of the working tree at `68247f92292ebaf2dd9cce58637ab83145b710ed`, plus pinned upstream sources. This report proposes authoring syntax. No new syntax, compiler support, proof, or native qualification was implemented during this investigation.

Post-review implementation: [the private state counter](../../examples/PrivateStateCounter.lean)
now uses readable scalar private-state declarations, typed witness callbacks,
`prove` conditions and staged writes. The compiler emits a source observation
summary. [The current guide](../development/typed-witnesses.md) records the
supported source fragment and protocol limits. The wider proposal below,
including complete public-activity policy and failure-channel analysis, remains
future work. The counter deliberately reveals its values through acceptance.

## Recommended model

Let authors compute with private values without repeatedly granting disclosure. Require explicit permission to release a value, reveal public activity, or make an intended acceptance claim. Keep permission to access wallet storage separate from all three.

Use the existing `disclose(value)` spelling for value release. Add readable private-state and witness declarations over the existing typed execution machinery. Introduce `prove predicate` for an authored claim whose truth becomes known when the transaction succeeds. Neither operation should make an underlying secret globally public. An optional `private let` should check an author's expectation about a local binding, not grant access or replace disclosure analysis.

Keep Lean as the language and compiler. Lower to the existing typed IR, native ZKIR and ledger plans. Compact offers useful design lessons, not a required parser, compiler, runtime, or capability ceiling.

## Four concepts authors must distinguish

| Concept | Meaning | Current implementation |
| --- | --- | --- |
| Public ledger state | Replicated contract data and observable reads/writes. Encryption changes the contents, not the visibility of the stored ciphertext or its key. | `StateDecl`, `StateKind`, `Effect`, `noctium_contract`. Scalar cells/maps and specific nested/record/byte-key paths exist. Broader token ADTs remain incomplete. |
| Private application state | Wallet-owned data retained between invocations, such as keys, plaintext caches and pending journals. There is no replicated secret ledger cell in this implementation. | Typed read providers, staged source writes, private journals, revision checks and the client lifecycle. The host owns storage confidentiality and durability. |
| Private circuit parameter | A value supplied for one invocation and constrained by its circuit. A parameter declaration neither loads nor persists anything. | `Input.visibility`, scalar `private` declarations, composite export inputs, canonical native input bindings. |
| Witness/provider callback | A host request which acquires an external value, possibly from private storage. “Witness” also names the private assignment used by the proof system, which is a broader cryptographic meaning. | `Helpers.WitnessSignature`, `Term.witnessCall`, typed callback validation, ordered Control execution and owned native handoff. Results remain untrusted and private. |

Private storage does not imply a useful ledger invariant. A wallet reporting “my balance is 100” proves nothing until the circuit relates 100 to the relevant authenticated ledger ciphertext, commitment, or authorization. Likewise, a correctly shaped witness reply proves only successful decoding. Its truth requires circuit constraints.

The prover and host receive private inputs. A remote proving service therefore belongs inside the confidentiality trust boundary. “Private from the network verifier” does not mean “hidden from every machine involved.” The official [witness guide](https://docs.midnight.network/guides/private-state-witnesses) makes the local-state/callback distinction and requires contracts to constrain witness results. Its TypeScript implementation pattern is comparison material only.

## What the implementation already enforces

`Nightlean/IR.lean` distinguishes parameter, provider and private-state origins. `Nightlean/Disclosure.lean:30` checks value origins separately from active control origins. Arithmetic, selection, hashing and Jubjub expressions propagate origins. Missing origin references fail closed.

`disclose` removes the wrapped expression's origins. `Nightlean/Semantics.lean:265` states its evaluation identity: the marker changes no value. The marker permits release downstream, rather than publishing data immediately or checking end-user consent. Place disclosure near the actual sink. Releasing `hash(secret)` should leave other uses of `secret` private.

The sink checks cover public circuit outputs, public ledger payloads, map keys, nested paths, membership/absence queries and supported state activity guards. Disclosing a constant inside a privately controlled branch does not authorize the branch's public activity. A public write of the same constant in one branch and no write in the other still exposes information through activity.

`Nightlean/Control.lean` and `Nightlean/ComponentDisclosure.lean` extend tracking through supported helpers, returns, aggregate components and private execution. A private branch used only for private work differs from a branch selecting public effects. Host callback schedules still reveal information to the invocation controller. They are outside the existing contract-public privacy observer.

`Nightlean/Witness.lean:10` retains stage-value evaluation when erasing private writes into the constraint program. The circuit does not prove the external storage mutation. `tests/WitnessSource.lean` exercises private reads, read-after-stage, repeated typed callbacks, result constraints, staged writes, Unit results and composite results. Authoring those examples currently requires substantial `Helpers.Program` structure construction. This is the largest immediate readability gap.

Typed private reads use declared fixed keys and scoped capabilities. Source stages currently support scalar values. The host journal supports more composite values than source staging. Source-bound invocations accept writes from their compiled stages, rather than arbitrary replacement journals. Typed curve inputs exist on the direct native path, but provider/control curve schemas and typed curve returns remain separate gaps. A type appearing in the scalar IR does not establish support through every execution route.

## Acceptance reveals a statement

The present disclosure pass deliberately does not classify constraints, proof success, failure or timing as ordinary value-flow sinks. `Disclosure.checkConstraints` visits expressions without demanding disclosure. `assertThen` similarly preserves body origins without treating success as a released value.

Consequently, this accepted relation reveals the entire secret:

```lean
private secret : UInt 8
public expected : UInt 8
assert eq(secret, expected)
```

The circuit's successful proof establishes equality with the public number. A Boolean access check reveals less, but still reveals a predicate. Repeated chosen thresholds or guesses also create a query channel when an observer sees outcomes.

The current PrivateClaim binds a computed private-derived nullifier to an already-public parameter and returns the public parameter. Its successful-only privacy theorem compares runs with equal public root, campaign and nullifier. This is a meaningful scoped claim. It is not secrecy of those values, resistance to guessing, or indistinguishable success and failure.

Recommended new source spelling:

```lean
prove eq(computedNullifier, suppliedNullifier)
```

Treat `prove` as an explicit acceptance claim and lower it to the existing constraint plus source policy metadata. Require this spelling for private-dependent, author-written assertions or requirements in the new ergonomic surface. Retain legacy `assert` semantics for compatibility. This is a circuit constraint declaration, not a Lean theorem tactic or an assertion about a theorem already proved. `prove p` authorizes learning that `p` holds on acceptance. It does not declassify the operands, publish the Boolean on rejection, or authorize privately guarded ledger writes.

This marker does not solve every failure channel. Checked arithmetic, casts, parsing, provider errors and resource exhaustion also affect completion. Generate a per-entrypoint observation summary listing public inputs, outputs, released expressions, ledger keys/activity, authored acceptance predicates and generated validity conditions. Separate local failures from observable submitted outcomes. Keep private values out of public diagnostics. The summary describes the policy. It is not a proof of all-outcomes privacy.

Do not require `disclose(secret)` before ordinary arithmetic or before constructing a relation. Such a rule releases more authority than the calculation needs and encourages broad markers near secret acquisition. If an application needs consent before accessing a medical record, for example, enforce consent in the host capability/provider policy. A source release marker does not enforce external authorization.

## Hashes, commitments and encrypted outputs

Keep all private-derived hashes, commitments and ciphertexts private until an explicit release at a public boundary. A low-entropy secret hashed without suitable hiding randomness is still guessable. A commitment needs its stated hiding/binding assumptions. Encryption needs the appropriate key, recipient, randomness and encoding assumptions. None follows from a `Bytes 32` or curve-point type.

The pinned [Compact disclosure document](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/explicit-disclosure.mdx) tracks arithmetic, indirect flows and hashes. It exempts selected commitment functions under an explicit randomness assumption. Adopt its close-to-sink release guidance and origin diagnostics. Do not adopt automatic commitment declassification as Noctium's default.

Publishing a ciphertext also reveals its existence, destination, length and public storage path. Publishing a new supply total exposes its delta. Public map keys reveal accessed accounts. The release policy must describe those observations, not merely exclude plaintext fields from a JSON object.

## Lessons from Compact's bounds

Comparison pin: Compact toolchain 0.36.1, source `7fa3a117c5e7efe9d2c51da04263e5f0b3509144`. Contract pin: OpenZeppelin Compact Contracts `f85f1a23685c6bbedfc8c2589ae3aa128aff7c46`. No Compact execution or dependency is needed for these conclusions.

### Numeric widths and conversions

Compact separates field arithmetic from bounded unsigned arithmetic. The [reference](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/compact-reference.mdx#primitive-types) provides bit widths and exclusive upper bounds. Its [type inference implementation](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/analysis-passes/infer-types.ss#L676) computes addition and multiplication using inclusive operand maxima, checks the supported maximum, and inserts a nonnegative-subtraction constraint. Narrowing casts check the target range.

Noctium's `ScalarPolicy.lean` already implements these ordinary unsigned rules. Two `UInt 8` operands add to `UIntRange 511`, covering 0 through 510. Their product needs `UIntRange 65026`, covering 0 through 65025. Casting 256 into `UInt 8` fails rather than truncating. Subtracting 1 from unsigned zero fails. `Native` subtraction wraps modulo the proving field instead. Use bounded integers for token quantities and counters. Use `Native` only when modular field semantics are intended.

Keep widths visible on parameters, persistent fields and return types. Infer temporary bounds. Prefer a diagnostic such as “sum requires values through 510, target permits 255” over exposing internal maximum representations. Preserve explicit checked narrowing. A convenience amount alias should preserve these rules, rather than silently wrap or hide a cast.

The 248-bit limit is currently both a Compact single-field integer choice and Noctium's implemented scalar policy. Compact explains its 31-byte packing rationale in [implementation limits](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/compact-reference.mdx#implementation-specific-limits). The native proving field modulus is a backend fact. “No integer wider than 248 bits is possible” is not a universal ZK limitation. Wider multi-limb integers would need distinct representation, arithmetic and native qualification, without silently changing the existing scalar contract.

Noctium's ordinary UInt-to-Native mixing currently chooses field semantics. New author examples should use explicit conversions at this boundary. A later strict money-oriented surface should reject accidental mixed arithmetic rather than encouraging a field cast to escape an unsigned overflow diagnostic.

### Fixed shapes, loops and indices

Compact requires compile-time finite circuit expansion. Fixed-size vectors, tuples, bytes and constant/generic loop bounds make cost and witness shape determinable. Its 16,777,216-element ceiling is a compiler resource choice, not a promise of practical proving cost. See [loop rules](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/compact-reference.mdx#for-statements).

Noctium already models finite composite layouts. Current default limits in `Types/Composite.lean:127` include vectors of 1024 elements, 4096 expanded leaves and 16384 expanded nodes. `Helpers.lean:150` independently limits source expansion, call depth and execution work. These are implementation budgets. Do not present them as Midnight language laws or automatically adopt Compact's larger ceiling.

For future readable collections, recommend `Bytes 32`, `Vector 32 Native` and `UIntRange 32` for a bounded index. Use the vector's length for `for item in values`, or a compile-time range for an indexed loop. Dynamic indexing must constrain the index and preserve selection semantics. A private vector index is not automatically a public ledger key. Whether its execution reveals access patterns depends on the backend and observer. General surface loops and every dynamic index path need their own support checks.

The [Compact standard library](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/standard-library.compact#L46) represents Merkle paths with a fixed-depth vector and computes roots with a fold. Adopt that readable shape. Keep hash domain tags and exact encodings in reviewed library functions, without making authors construct backend limbs or unroll a path by hand.

### Ledger collections are a different boundary

The [ledger ADT reference](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/ledger-adt.mdx) describes growing maps, sets and lists, plus depth-bounded Merkle trees. Finite circuit work does not require every stored map to have a compile-time number of entries. Expose bounded operations per invocation, not an unrestricted loop over the whole ledger.

Keep missing-key semantics, membership checks, insertion, replacement and counters explicit. A generic zero default is unsafe for some crypto types. OpenZeppelin initializes valid encrypted-zero points and nested map entries before use. The author-facing API should provide typed domain defaults, not reinterpret all-zero bytes as a valid curve point.

### Witness and runtime bounds

External values need exact shapes, widths, lengths, enum tags and canonical encodings even when the host language has static types. This is explicit in Compact's [external-value checks](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/doc/compact-reference.mdx#implementation-specific-limits). Noctium's `runtime/src/witness.rs` and aggregate codecs already enforce corresponding typed boundaries for supported routes. Circuit constraints must separately reject a dishonest well-formed reply.

Keep provider signatures readable, such as `plaintextBalance(ciphertext : Ciphertext) : UInt 248`. Generate operation versions, schema fingerprints, canonical leaf traversal, call-site identifiers and transport envelopes. The host explicitly binds an implementation and grants capabilities. The contract body should not contain request IDs, byte buffers, journal digests or process handles.

Request counts, schema bytes, source expansion and private-buffer budgets protect availability. They belong in a versioned compiler/runtime capability report with clear diagnostics. Business bounds, such as a transfer ceiling or path depth, belong in source. A `Bytes 32` randomness result establishes shape only. It establishes neither entropy nor freshness.

Jubjub deserves a separate type boundary. `runtime/src/jubjub.rs` distinguishes strict scalar input validation from explicit scalar reduction, and decodes points through a subgroup-checked path with coordinate round-trip checks. Keep `JubjubScalar` distinct from `Native`. Never silently reduce a malformed external scalar. Pin the exact chosen derivation when porting a crypto helper, since truncation and modular reduction are not interchangeable specifications.

### Lessons from a real token

The pinned [ConfidentialFungibleToken](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/token/ConfidentialFungibleToken.compact) uses 128-bit transfers and 248-bit balance claims. Its source explains why accumulation needs more room than a single transfer, while acknowledging sufficiently large accumulation eventually exceeds the scalar encoding. This is a documented bound, not a proved unbounded supply guarantee.

Its plaintext callback receives the actual ciphertext. `_debit` checks the returned balance through decryption/key binding before checking available funds. The provider's cache does not become authoritative merely by returning a number. Its ciphertext maps, nested escrow, counters and memos also show why aggregate codec support alone does not complete the ledger API.

Fresh secret randomness remains a wallet responsibility. The token documents deterministic seed expansion, reuse risks and exposed counterparties/counters. Model these as named assumptions. Do not label freshness circuit-proved. Its [public-supply extension](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/token/extensions/ConfidentialFungibleTokenPublicSupply.compact) checks overflow/underflow and deliberately publishes mint/burn deltas. Composition must couple token changes with supply changes. An encrypted balance does not hide an amount also exposed through public supply.

## A small coherent source surface

Retain `import Noctium.Frontend`, `open scoped Noctium`, `noctium_circuit` and `noctium_contract`. Add declaration sugar and a body form for `noctium_witness_circuit`. Lower those additions to existing `Helpers.Program`, signatures, stages, circuit outputs and ledger effects. Do not create a second interpreter.

Recommended forms, all proposed unless already supported:

| Source form | Meaning |
| --- | --- |
| `noctium_private_state Wallet ...` | Typed local schema. Generates stable storage descriptors and read signatures. Host supplies namespace and grants. No public ledger allocation. |
| `noctium_witness lookup(...) : T` | Typed untrusted acquisition. Host registration supplies a versioned operation/capability binding. |
| `read private Wallet.field as value` | Read through the scoped provider and current staged overlay. |
| `stage Wallet.field := value` | Tentative source-owned update. No immediate durable commit. |
| `let name : T := expression` | Infer privacy from inputs. Optional `private let` checks privacy retention. |
| `prove predicate` | Authored acceptance predicate, with checked policy metadata. |
| `disclose(expression)` | Permit the expression's value to reach a public sink. |
| Existing `cell`, `map`, `read`, `write` in a contract | Public ledger state. Document this explicitly. An additive `ledger` label is optional readability work, not a prerequisite. |

Keep function/helper returns private inside the program. Exported outputs remain public unless a separate private host-return API is explicitly introduced. Do not infer return visibility from the word “circuit.” Source disclosure classification is separate from proof-statement authentication. A standalone native `Output` does not automatically become a bound public proof instance. The contract CALL path needs its actual transcript and communication binding. Ordinary Lean theorem authoring remains unrestricted by the finite runtime subset.

### Example 1: private storage used in arithmetic

Proposed syntax, not currently compilable as written:

```lean
import Noctium.Frontend
open scoped Noctium

noctium_private_state Wallet where
  cell saved : UInt 8
  cell draft : UIntRange 511
end

noctium_witness_circuit prepareDraft where
  private increment : UInt 8
  read private Wallet.saved as saved
  let next : UIntRange 511 := add(saved, increment)
  stage Wallet.draft := next
end
```

The largest sum is 510. No private-derived value is released. The stage remains tentative and requires a transaction lifecycle to become durable. This example does not claim the host's initial saved value is authenticated by the ledger, or that local request timing is hidden from the host.

### Example 2: intentional public release

This uses the existing scalar surface. It was inspected, not executed during this research:

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit publishTotal where
  private left : UInt 8
  private right : UInt 8
  let total : UIntRange 511 := add(left, right)
  output result : UIntRange 511 := disclose(total)
end
```

The policy releases the sum. It does not promise secrecy of either operand against auxiliary knowledge. If the observer knows one operand, the sum reveals the other. Removing `disclose` should reject at the public output. A public ledger write using this output still requires the contract's normal authorization relation.

### Example 3: constrained witness and staged private update

Proposed scalar source sugar over the existing witness machinery:

```lean
noctium_witness nextValue(previous : UInt 8) : UInt 8

noctium_witness_circuit advanceCounter where
  public expected : UInt 8
  read private Wallet.saved as previous
  let next : UInt 8 := witness nextValue(previous)
  prove eq(next, cast(UInt 8, add(previous, uint(1))))
  prove eq(next, expected)
  stage Wallet.saved := next
  output nextCount : UInt 8 := expected
end

noctium_contract CounterReceipt where
  cell count : UInt 8
  entry advance uses advanceCounter where
    read count as current
    require eq(add(current, uint(1)), expected)
    write count := nextCount
  end
end
```

The callback must return the successor, and the ledger relation must advance the current public counter by one. Adding one to a UInt 8 produces an inferred maximum of 256, requiring UIntRange 257. The explicit checked cast back to UInt 8 rejects an attempt to advance 255. The private stored value is a local cache of public data in this small example. Both equality predicates deliberately disclose its relationship to the public count. Real private token balances should instead bind a ciphertext-indexed witness to authenticated ciphertext and key ownership, as described above, without publishing the plaintext.

No contract statement performs a durable commit. The application submits the owned invocation through the normal client. Its user-facing outcome distinguishes pending/uncertain, rejected, finalized with private state saved, and finalized with a private-state conflict. A conflict after finality never means the chain transaction was rolled back.

## Finality and storage guarantees

Use the owned `WitnessExecution` → `WitnessProof` → `WitnessProvedCall` → `WitnessClient` path for public examples. `runtime/src/witness_execution.rs` freezes the authenticated target and carries the same invocation into proof and client ownership. It does not accept a replacement input map or arbitrary journal at the handoff.

`runtime/src/client.rs:441` checks network policy, height, transaction/intent identity, address, expected event and exact predicted contract state. `observe_once` validates a finalized receipt before recording acceptance. `commit_private` also requires observed evidence before the store's compare-and-exchange. The journal binds the attempt, transaction, target, base revision and full private payload. Retries use durable receipts to avoid applying the same update twice.

`runtime/src/localnet.rs` correlates the exact submitted extrinsic, finalized ancestry, applied/contract events and canonical state. Its node/RPC is trusted. This is not a consensus light client. `runtime/src/localnet_store.rs` provides a development filesystem store and explicitly treats the directory as trusted. Hashes detect corruption and correlate records, rather than resisting a malicious host rewriting storage.

The lower-level `host.rs` accepted notification still trusts the host. Do not expose an application-friendly `commit(true)` wrapper around that seam. `docs/designs/private-state-lifecycle.md` describes an older transport package and understates later source stages, recovery and validated client support. Use `docs/development/typed-witnesses.md` plus current code for present integration behavior.

The host's durable storage, atomic CAS and finality service remain assumptions. A source theorem about private stages does not prove a database write. `recordInvocation_replayInvocation_matches` and `validateCompleteInputMap_preserves_bindings` in `Nightlean/Witness/Semantics.lean` cover admitted recording/replay and exact bindings under their stated validation/trace premises. They do not prove every compiler transformation or callback implementation.

## Public examples and historical evidence

At inspection, `examples/Disclosure.lean`, `examples/PrivateClaim.lean` and `examples/openzeppelin/PublicSupply.lean` still use `Nightlean` imports/scopes or commands. `examples/BoundedScalars.lean` already uses Noctium. “Nightly” is not the actual legacy identifier in these files.

Concurrent parent work is migrating the ordinary disclosure and public-supply examples and adding `examples/NoctiumPrivateClaim.lean` as the branded teaching copy. The original `examples/PrivateClaim.lean` path and source SHA remain unchanged. These edits follow the research baseline above and do not extend its historical proof receipts.

Migrate the ordinary disclosure and public-supply examples to Noctium aliases, preserving declaration names. Check their direct CLI consumers. Add new readable witness examples under `examples/`, rather than asking authors to learn from `tests/WitnessSource.lean`.

Preserve `examples/PrivateClaim.lean` at its existing path and bytes. Proof modules import it, and deployment auditing explicitly binds its path and hash. Add a separate Noctium-branded teaching copy with a distinct namespace. Point authoring links to the new example, and label the old file as the qualified historical source in surrounding documentation. Do not edit its header merely to explain its historical status.

The exact private-claim source authority is `925164d0e17d994038d77d3b2b71c410619557d3`. Its deployment implementation qualification separately records `c48fc4b7aa1a06926c15fb83026fb51ce80c203c`. Typed-witness qualification records `b1afd9f4afa9525a5031820ab7eeaaddbee7e299`. Preserve retained manifests, proof identities, ABI identifiers, wire names and receipt bytes. A new branded example does not inherit an exact-source receipt merely because its computation appears equivalent.

Relevant records: [private-claim certificates](../development/private-claim-artifact-certificates.md), [deployment audit](../development/private-claim-deployment-audit.md), [typed-witness qualification](../development/typed-witness-qualification.md), and [retained witness evidence](../../tests/witness62-public/README.md). Branding alone does not justify an expensive proof requalification.

## Delivery order and minimum acceptance

1. Correct ordinary public examples and add the branded claim teaching copy. Keep historical evidence immutable. Run the directly affected source/CLI checks once. Parent work owns these edits.

2. Implement [#73](https://github.com/awjreynolds/noctium/issues/73), the focused authoring package for private-state declarations, witness signatures and the readable witness body. Reuse completed [#62](https://github.com/awjreynolds/noctium/issues/62). Generate metadata and scope resolution rather than requiring handwritten numeric declaration IDs. Compile a scalar read/call/stage example. Run one existing owned native witness path with that source and one malformed/dishonest callback case. Do not reopen completed witness transport as a new architecture project.

3. Extend [#45](https://github.com/awjreynolds/noctium/issues/45) with `prove` policy metadata and the generated observation summary. Preserve legacy assertions. One explicit private-value leak, one private activity/key leak, and one public-parameter equality case establish the new authoring boundary. Keep failure-channel scope visible. Reuse existing disclosure tests for unchanged sinks.

4. Continue [#43](https://github.com/awjreynolds/noctium/issues/43), [#70](https://github.com/awjreynolds/noctium/issues/70) and [#69](https://github.com/awjreynolds/noctium/issues/69) according to the token workload. Keep bounds, canonicality, crypto derivations and per-operation guards together with each feature. Complete provider/control curve schemas and token witness interfaces before claiming the typed token path works. Use one focused native example per changed feature group, plus a targeted negative when its boundary needs one.

5. Complete the current-state and multi-entrypoint integration in [#67](https://github.com/awjreynolds/noctium/issues/67), then the integrated token lifecycle in [#68](https://github.com/awjreynolds/noctium/issues/68). Verify repeated calls observe the actual prior state, and expose finalized/private-conflict as a distinct outcome. Keep one integrated localnet demonstration for the completed port.

6. Use [#21](https://github.com/awjreynolds/noctium/issues/21) for source/native preservation and explicit privacy obligations, and [#23](https://github.com/awjreynolds/noctium/issues/23) for independent production review. These remain release assurance work. They should not turn every syntax or branding edit into a new proof-export campaign.

The recommended defaults need no additional product decision: inferred private computation, explicit value release, explicit authored acceptance claims, typed bounded data, tentative private writes and client-controlled commit after validated finality. The investigation created no GitHub issues or comments. Parent follow-up records the authoring package in #73 and the scoped policy work in #45.

Skipped: builds, test execution, proof generation, deployment and broad security auditing. Proposed syntax and wider token support remain unimplemented, and existing evidence applies only to its recorded source and assumptions.
