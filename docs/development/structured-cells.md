# Structured helper bodies with native cell state

A structured helper body now expresses typed cell reads and writes alongside lexical bindings, helper calls and guarded branches. The compiler lowers these statements to the existing ordered `Entrypoint.effects` and `effectGuards`, then uses the native Impact and ZKIR backends. This adds source capability without introducing a new native opcode.

The [source example](../../tests/StructuredCells.lean) declares its required ledger schema in `Helpers.Program.ledger` and attaches the export to an owning contract:

```lean
noctium_contract StructuredCells where
  cell balance : Native
  entry update from structuredCellProgram entry "update" end
end
```

Its typed body uses these statement forms:

```lean
.readCell "balance" "before" .native
.writeCell "balance" .native
  (.binary .add (.ref "before") (.ref "amount"))
```

A read binds a fresh typed local name to the state at that point in the operation sequence. Writes and later reads retain source order. Branch-local names stay inside their lexical scope. A helper result becomes a proof-bound entrypoint return after the effects, rather than a standalone circuit output referring to unavailable ledger values.

## State authority and privacy

`Helpers.compileEntrypointFor` checks the helper's required declarations against the owning contract's actual schema, including cell type and sealed status. The exporter rebuilds structured entries from their registered source program before validating and lowering the owning contract. Cached generated entries do not replace this source check.

A private condition controlling a public cell write needs explicit disclosure, even when the written value is constant. A private payload needs its own disclosure. The generated entrypoint passes the existing mandatory disclosure analysis. A public ledger read does not release unrelated private inputs.

Assertions and partial computations retain guarded evaluation. Inactive branches skip their cell operations and use the existing canonical read defaults. Active invalid casts retain their failure. Strict bindings still evaluate when their result is unused.

## Current boundary

This source route currently supports scalar cells. Maps, aggregate state and provider/private-state scheduling inside the same helper body remain follow-up work under [structured native control](https://github.com/awjreynolds/noctium/issues/43). Existing contract effect blocks retain their broader state operations. Ordinary `Helpers.compile` and portable host-control plans reject ledger statements. `stage` retains its private journal meaning.

The source route follows the existing helper resource policy, including at most 256 ledger declarations in the owning schema. Results are scalar or Unit. Byte, curve and composite cell values remain on the existing contract effect route.

The owning schema and existing backend remain authoritative. This source extension does not establish whole-compiler preservation, complete Compact equivalence or production readiness. The previously qualified claim remains a separate evidence scope.

## Focused evidence

Implementation revision: `0ab7fd38ee952ab5d1a69ced4dc33f4de9d04059`.

The [native case](../../runtime/tests/structured_cells.rs) consumes source-generated ZKIR and Impact plans with the pinned 3.2.1 checker. Starting from balance 3, the disclosed active branch adds 7 and returns 10. The inactive branch preserves balance 3 and returns 3 despite an invalid branch-local narrowing input. An active invalid input and a changed private guard reject. Source checks reject an undisclosed write guard and a mismatched cell read type.

The older optional `Noctium.Witness.Semantics` module still has unmatched Boolean, byte and curve term/value families. A baseline source check reproduces these gaps. The new state statements are explicitly rejected by its bounded replay model, and this extension has no fresh witness-model or generic preservation qualification. Repair belongs to the open [semantic-preservation work](https://github.com/awjreynolds/noctium/issues/21).

No new keys, proofs, deployments or K benchmark accompany this source extension. The native checker and exact local state assertions supply the focused integration evidence.

The 73-job compiler/Claim build and source export pass. The new native case and one existing helper case each pass in 0.01 seconds. Recompiling the existing helper preserves its native circuit and Impact plan byte-for-byte.
