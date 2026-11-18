# Anonymous operators, map and fold

`Noctium.Helpers.Iteration` constructs ordinary checked Helpers declarations and call terms at compile time. The implementation is Lean. Its output follows the existing direct ZKIR, native ledger and host-neutral witness paths.

An operator names an existing helper or supplies an anonymous statement body. Missing parameter annotations come from actual argument types. A missing result annotation comes from the body returns. The compiler captures referenced outer values as typed arguments. Parameter and block bindings retain their lexical scopes. Generated declarations still pass ordinary helper checks. Frontend source references use Lean name resolution, including private definitions.

## Source construction

The API returns an updated `Helpers.Program` and the resulting `Helpers.Term`. Thread the updated program into subsequent construction, then put the returned term in the caller's body. `scope`, `env` and `span` identify the caller's lexical context. The [complete source example](../../tests/IterationWitness.lean) shows this assembly.

```lean
let (mappedProgram, mapped) ← Iteration.mapWithLimits {} base 0 env {}
  [.ref "values"]
  (.anonymous [{name := "value"}] none [
    .return (some (.binary .add (.ref "value") (.ref "offset")))])

let (foldedProgram, folded) ← Iteration.foldWithLimits {} mappedProgram 0 env {}
  (.native 0) [mapped]
  (.anonymous [{name := "acc"}, {name := "value"}] none [
    .return (some (.binary .add (.ref "acc") (.ref "value")))])
```

`applyWithLimits` applies an operator to ordinary argument expressions. `mapWithLimits` accepts one or more fixed sequence expressions and requires equal lengths. Its operator receives one element from each sequence. `foldWithLimits` accepts an initial value and a list of equal-length sequences. Its operator receives the current accumulator and one element from each sequence. Supported sequences include vectors, vector-compatible tuples, scalar byte strings and checked composite byte layouts. Tuple elements need a common type under the supported subtype rules. Byte elements use the bounded range 0..255. Empty tuples currently reject because they provide no element type; typed empty vectors and bytes remain supported.

Generated wrapper parameters evaluate each complete sequence once. Fold evaluates its initial expression before its sequence expression. Ordered bindings retain operator calls and partial computations. Empty vectors keep their declared element type, so checking the operator does not require indexing a nonexistent element. Existing source, type, parameter, declaration and finite expansion limits apply. Checked layout costs bound result projection expansion before cloning. Zero-field results retain strict evaluation tokens, so binding a Unit or empty aggregate does not discard its assertions or partial computations.

Fold requires the accumulator parameter and result types to match exactly. The initial expression accepts a narrower compatible type. Map results use checked scalar, Unit, tuple, record, nested vector, byte and enum layouts. The compiler projects their canonical leaves into the result vector. Enum tag projections return the checked Native variant ordinal. Payload projections run only under their matching tag, and shorter variants retain canonical zero padding. Nested enum payloads use the same rule. Unit parameters and captures retain their logical argument positions while contributing zero native fields. Additional sequence forms need further implementation. Anonymous operators support ordinary structured statement bodies, including their own returns. Public effects and outputs still require explicit disclosure of private values and controlling conditions.

Reading `.enumTag` returns the tag as data. `disclose` around this projection authorizes release of the tag value. The payload stays private. Selecting a variant's payload also depends on its tag, so disclosing only the payload does not release the private tag or earlier private selection conditions.

## Unit arguments

A Unit helper parameter uses a logical parameter plus a `compositeParameters` entry whose type is `.unit`. A root Unit input occupies one `Export.compositeInputs` row with type `.unit`. Typed host plans retain its name, visibility and `Unit` schema. The native circuit receives no placeholder Boolean or field input.

Hosts supply the canonical value `{"kind":"unit"}`. A missing logical Unit argument still rejects. Unit-valued argument expressions retain strict evaluation, including failing computations, even though their value has no data fields. Anonymous captures and generic specializations use the same representation.

## Focused execution evidence

The [native case](../../runtime/src/witness_execution/iteration_ledger_tests.rs) consumes artifacts generated from `IterationWitness.lean`. Its expected provider order is:

1. `touch` returns Unit. The caller binds this value, passes it to an anonymous operator and captures it in map.
2. `seed` returns 0 after the Unit argument evaluates.
3. `values` returns the private tuple `[1,2,3]` once. Its middle element has type `UInt3`; the surrounding Native elements give the tuple a common Native element type.
4. Three `double` calls receive 3, 4 and 5 after adding captured private offset 2. They return 6, 8 and 10.

Each mapped record contains an enum amount and a nested two-element metadata vector. The middle input produces the empty amount variant. The other two contain amounts 6 and 10. Fold reads each enum tag and conditionally projects the active payload alongside byte fees `[1,2,3]`. The two-sequence fold sums the amounts and fees to 22. The source asserts the expected result, explicitly discloses the public cell write and stages private value 22. The inactive branch makes no provider calls and preserves total 0. A wrong provider value rejects before the write and private stage. Completed paths run through the native checker. A source rejection also removes the write disclosure and checks the private value is rejected at the public sink.

This is staged Lean source construction, with explicit Helpers statements. Readable operator syntax, empty-tuple inference, wider structural subtype joins and generic operator preservation remain open under [issue 48](https://github.com/awjreynolds/noctium/issues/48). Source and native checker cases do not establish full Compact equivalence or whole-compiler preservation. A conservative closure pass omits unused bindings only when their value and creation guard are total in the checked Native context. Partial and unknown expressions retain their order and guard totalization. At the [record-only checkpoint](https://github.com/awjreynolds/noctium/commit/02beefa6f7a2352b00387f04fc6ed931b34f3b86), the Impact plan fell from 25,167,866 to 3,309,220 bytes and ZKIR occupied 15,583 bytes. The current example also exercises Unit arguments, captures and a logical Unit root input. The native test rejects omission of that root input and checks its empty native binding list. The current nested-enum export occupies 3,105,625 bytes for Impact and 92,156 bytes for ZKIR. The native case passes in 0.21 seconds, excluding compilation. This workload adds guarded enum construction and projection, so these sizes do not form a matched optimisation comparison. Redundant total-value forcing is omitted, while explicit constraints and partial checks remain. Raw composite witness field bounds are unconditional circuit input requirements, including inactive defaults. These are artifact sizes, without a proof-time or K claim. Broader expression sharing stays in [optimisation issue 85](https://github.com/awjreynolds/noctium/issues/85). No keys, proofs, deployments or new K benchmark accompany this extension.
