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
  (.native 0) mapped
  (.anonymous [{name := "acc"}, {name := "value"}] none [
    .return (some (.binary .add (.ref "acc") (.ref "value")))])
```

`applyWithLimits` applies an operator to ordinary argument expressions. `mapWithLimits` accepts one or more fixed vector expressions and requires equal lengths. Its operator receives one element from each vector. `foldWithLimits` accepts an initial value and one fixed vector expression. Its operator receives the current accumulator and next element.

Generated wrapper parameters evaluate each complete sequence once. Fold evaluates its initial expression before its sequence expression. Ordered bindings retain operator calls and partial computations. Empty vectors keep their declared element type, so checking the operator does not require indexing a nonexistent element. Existing source, type, parameter, declaration and finite expansion limits apply.

Fold requires the accumulator parameter and result types to match exactly. The initial expression accepts a narrower compatible type. Current map results use scalar types accepted by the existing checked vector layouts. Unit parameters and captures reject. Composite map results and additional sequence forms need further implementation. Anonymous operators support ordinary structured statement bodies, including their own returns. Public effects and outputs still require explicit disclosure of private values and controlling conditions.

## Focused execution evidence

The [native case](../../runtime/src/witness_execution/iteration_ledger_tests.rs) consumes artifacts generated from `IterationWitness.lean`. Its expected provider order is:

1. `seed` returns 0.
2. `values` returns the private vector `[1,2,3]` once.
3. Three `double` calls receive 3, 4 and 5 after adding captured private offset 2. They return 6, 8 and 10.

Fold sums these values to 24. The source asserts the expected result, explicitly discloses the public cell write and stages private value 24. The inactive branch makes no provider calls and preserves total 0. A wrong provider value rejects before the write and private stage. Completed paths run through the native checker. A source rejection also removes the write disclosure and checks the private value is rejected at the public sink.

This is staged Lean source construction, with explicit Helpers statements. Readable operator syntax, remaining sequence/result forms and generic operator preservation remain open under [issue 48](https://github.com/awjreynolds/noctium/issues/48). Source and native checker cases do not establish full Compact equivalence or whole-compiler preservation. The consumed Impact plan occupies 1,812,690 bytes and ZKIR occupies 11,479 bytes. Expression sharing stays in [optimisation issue 85](https://github.com/awjreynolds/noctium/issues/85). No keys, proofs, deployments or new K benchmark accompany this extension.
