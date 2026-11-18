# Structured helper bodies with native state

Structured helper bodies express typed cell reads, map reads, membership queries and writes alongside lexical bindings, helper calls and guarded branches. The compiler lowers these statements into the existing ordered `Entrypoint.effects` and `effectGuards`, then uses the native Impact and ZKIR backends. This adds source capability without a new native opcode.

## Authoring

The [cell example](../../tests/StructuredCells.lean) declares its required state in `Helpers.Program.ledger` and attaches the export to an owning contract:

```lean
noctium_contract StructuredCells where
  cell balance : Native
  entry update from structuredCellProgram entry "update" end
end
```

The [map example](../../tests/StructuredMaps.lean) uses the same entrypoint form with `map balances : Bytes32 => Native`. Its helper body uses typed statements:

```lean
.readMember "balances" "present" (.bytes 32) .native (.ref "key")
.readMap "balances" "previous" (.bytes 32) .native (.ref "key")
.writeMap "balances" (.bytes 32) .native (.ref "key")
  (.binary .add (.ref "previous") (.ref "amount"))
```

Membership binds a Bool. A value read binds the declared map value type. Reads observe state at their position in the operation sequence, including earlier writes. A value read requires an existing entry, so the example queries membership before reading. Inactive reads use the backend's canonical defaults without accessing a missing entry. Lexical bindings, nested guards and early returns retain their source scope and order.

A helper result becomes a proof-bound entrypoint return after the effects. Ledger values therefore use the existing transcript binding instead of becoming references in a standalone circuit with no ledger context.

## State authority and disclosure

`Helpers.compileEntrypointFor` checks required declarations against the owning contract's actual schema, including state type and sealed status. The exporter rebuilds entries from their registered source program before validating and lowering the contract.

Private lookup keys need explicit disclosure before addressing a public map. Membership queries also expose the lookup path. A private condition controlling a public read or write needs disclosure, including a constant write. Releasing a payload does not authorize a private key or condition. The generated entrypoint passes the existing mandatory disclosure analysis.

Assertions and partial computations retain guarded evaluation. Active invalid casts fail. Strict bindings still evaluate when their result is unused.

## Current boundary

This route supports the existing scalar value types: Native, Bool, bounded UInt, fixed bytes, Jubjub scalar/point and the registered foreign field/curve families. Key types follow the existing ledger validation. The native map cases exercise Bytes32 keys with Native and Bytes33 values. The helper resource policy bounds the owning schema to 256 declarations, and results are scalar or Unit.

Typed providers and private staging now share the same structured body with ordered state effects. Aggregate values, nested ledger trees and complete proof/ledger qualification remain under [structured native control](https://github.com/awjreynolds/noctium/issues/43). Existing contract effect blocks retain broader state operations. Ordinary `Helpers.compile` and portable host-control plans reject ledger statements. `stage` retains its private journal meaning.

## Focused evidence

The [native cell case](../../runtime/tests/structured_cells.rs) was introduced in `0ab7fd38ee952ab5d1a69ced4dc33f4de9d04059`. Starting from balance 3, the active branch adds 7 and returns 10. The inactive branch preserves 3. Its essential source and native rejection checks are recorded in that revision.

Map implementation revision: `fc5f3afb290c895135b5f92f4d2383312330577d`.

The [native map case](../../runtime/tests/structured_maps.rs) consumes the source-generated circuit and Impact plan with the pinned 3.2.1 checker. One scenario checks:

| Starting entry | Enabled | Amount | Returned value | Final entry |
| --- | --- | ---: | ---: | --- |
| absent | false | 8 | 0 | absent |
| absent | true | 7 | 7 | 7 |
| 7 | true | 2 | 9 | 9 |
| 9 | false | 8 | 9 | 9 |

The false calls skip branch-local UInt narrowing despite amount 8 exceeding the declared maximum 7. The active invalid input and altered private guard reject. Source checks reject an undisclosed private map key and a wrong key type.

State-only cases retain their consumed circuit and ledger plan. Witness cases also retain their binding and control plan. No new keys, proofs, deployments or K benchmark accompany this source extension. Native checker and local state assertions are integration evidence, not complete language equivalence or generic compiler preservation.

The optional historical `Noctium.Witness.Semantics` model still has unmatched older Boolean, byte and curve families. Cell/map statements are explicitly outside its bounded replay model. Its repair and broader preservation qualification remain under [semantic preservation](https://github.com/awjreynolds/noctium/issues/21).

The current compiler build, source export and focused native map case pass. The native case runs in 0.02 seconds after compilation. The shared native build directory occupies 1.1 GiB with the POC build settings.

## State-dependent typed witnesses

The [source example](../../tests/StructuredLedgerWitness.lean) reads balance 3, passes that value to the `derive` witness, explicitly discloses the computed update, writes the balance and reads the updated value. Private staging follows the source assertions. The same `entry ... from ...` form emits its typed witness binding and control plan alongside the native circuit and Impact plan.

`WitnessExecution.advance` handles internal ledger callbacks through its owned `PreparationCursor`. Applications receive only external provider requests. Generated read slots are constrained equal to their actual native ledger reads. This equality permits treating those slots as public ledger data. Applications cannot supply a ledger read through `resume_typed`. Callback metadata binds each internal call to its source ordinal and native operation boundary, with read name/type checks against the selected plan.

The cursor keeps one native execution prefix, so a later read observes earlier writes. No second host ledger interpreter runs. The authenticated deployment target or admitted current-state token supplies the starting state. Candidate writes remain local until the existing proof, client and private-journal lifecycle accepts the operation. Cancellation retains the original admitted state for retry.

The focused Rust case covers balance 3, provider result 7, updated balance/return 10 and staged private value 7. The inactive branch skips the external provider, returns 0 and preserves balance 3. A wrong provider result fails before private staging. The case also rejects an externally forged internal read response and a callback redirected to another native read. Both completed paths pass the pinned 3.2.1 checker.

This source integration uses scalar cell/map values and scalar or Unit results. Native and typed byte/curve cases have scoped runtime evidence below. Aggregate state bodies, portable bindings and general source-preservation proofs need separate evidence. No new opcode, key, proof or deployment accompanies this slice.

State-dependent witness implementation revision: `4b3b37e018ed5f8406caa3a91bcbf3428d9925a5`. Four focused runtime cases pass in 0.02 seconds. Two existing guarded-witness cases pass in 0.01 seconds. The compiler and source export pass.

## Typed byte and curve state

The [typed source contract](../../tests/StructuredTypedCells.lean) uses Unit helpers to read cells, call typed providers and explicitly disclose their results into writes. Its cells hold Bytes33, Bytes0, JubjubScalar, JubjubPoint and Secp256k1Base. A Bytes32-keyed map holds Bytes33. One disclosed private guard controls all calls.

A provider receives the logical value, including a complete byte array or point. The compiler and runtime bind physical read fields to that value. Byte reads carry exact chunk projections, point reads carry ordered coordinates, and foreign relation inputs retain their exact native type. Empty byte reads have no physical fields but still execute their source callback and ordered ledger effects.

The focused [Rust case](../../runtime/src/witness_execution/typed_ledger_tests.rs) checks all six provider arguments, returns changed valid values and compares the complete native successor state with the expected typed cells/map. The inactive branch preserves state without callbacks. Invalid byte length rejects before a corrected response resumes the pending provider. Reordered point projections and a foreign input relabelled as a BLS scalar reject during artifact validation.

The source type gate covers registered scalar families. This combined native case samples one foreign field family. Other foreign overloads, nested/aggregate helper state, exotic map keys, portable bindings and general preservation remain separate obligations. No new opcode, key, proof or deployment accompanies this extension.

Typed state implementation revision: `fe73696b64e3d1170aab3e31a17f3ae97b799d6a`. The compiler, source export, byte semantics and eight combined/previous runtime cases pass. The native cases finish in 0.04 seconds.


## Finite range loops

Structured programs accept a half-open compile-time range:

```lean
.forRange "index" 1 4 [
  .readCell "total" "before" .native,
  .bind "delta" (.scalar .native)
    (.witnessCall "range-step" "step" [.ref "index", .ref "before"]),
  .writeCell "total" .native
    (.disclose {} (.binary .add (.ref "before") (.ref "delta"))),
  .stage "private" "loop/last" .native (.ref "delta")]
```

The Native index is local to each iteration. Bounds must be ordered constants no greater than `2^248 - 1`. Each range has at most 1,024 iterations. A saturating nested expansion budget rejects oversized bodies before cloning. Empty ranges still typecheck their bodies. Returns inside a loop body reject, including unreachable returns. A called helper retains its own return scope.

Circuit loops expand statically. Each cloned witness call receives a distinct site identity. Constant scope branches lower only their selected path, avoiding repeated copies of the remaining iterations. Later effects exclude expired iteration-local bindings. Dynamic branch lowering retains its existing guarded continuation behavior.

The three-iteration fixture initially occupied 1,954,016 bytes for its Impact plan and 42,783 bytes for ZKIR. Selecting constant branches once and excluding expired iteration bindings reduces these to 226,696 and 13,710 bytes respectively. This measures artifact size, without a new timing, K or proof benchmark.

The [source example](../../tests/FiniteRangeWitness.lean) performs three ordered read/provider/write/stage iterations. Its [native case](../../runtime/src/witness_execution/range_ledger_tests.rs) checks provider inputs `(1,0)`, `(2,1)`, `(3,3)`, final public total 6 and staged private value 3. An inactive outer branch makes no provider calls, stages no writes and preserves total 0. Both completed paths pass the selected native checker.

This is a structured Helpers API, without new surface loop grammar or native opcodes. [Generic ranges](generics.md#generic-finite-ranges) resolve compile-time Nat expressions through the same preparation path. Anonymous functions, container iteration, map/fold and general loop preservation remain open under [issue 48](https://github.com/awjreynolds/noctium/issues/48). No new keys, proofs, deployments or cross-profile campaign accompany this slice.
