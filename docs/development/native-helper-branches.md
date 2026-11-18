# Native structured helper branches

Structured helper branches and lazy `ite`, `andThen` and `orElse` expressions compile through `noctium_helper_circuit` into the existing native backend. They use the same [guarded expression transformation](../../Noctium/GuardedExpression.lean) as contract effects. This adds source control-flow capability without adding a ZKIR opcode.

An inactive branch's assertions and fallible casts receive safe guarded operands. Active paths retain their failures. Each generated expression binds its condition before branch selection. Branch-local names stay inside their lexical scope, and an early return skips the enclosing continuation. Scalar, unit and checked aggregate results retain their respective value and constraint representations. Zero-leaf aggregate results retain sequencing failures through an explicit constraint.

The [Source fixture](../../tests/NativeHelperBranches.lean) binds an outer value, shadows its name inside a conditional branch, checks a value and narrows it, then returns the outer value. An existing contract entrypoint uses the resulting circuit to guard a cell update:

```lean
noctium_contract NativeHelperBranches where
  cell balance : Native
  entry update uses nativeBranchValues where
    if disclose(enabled) then {
      write balance := result
    } else {
    }
    return observed : Native := result
  end
end
```

The helper's private Bool condition also needs explicit disclosure before controlling its public result. Disclosing a payload alone does not authorize its private control dependencies. Source validation still checks inactive branches and rejects unsupported types, effects and oversized programs.

## Execution boundary

This path compiles witness-free structured helper control into native circuit expressions, then connects those results to the established contract effect API. It does not add ledger-effect statements inside `Helpers.Program` bodies. It does not reinterpret private host `stage` operations as public ledger writes.

Ordinary helper compilation retains its guarded-witness gate. The separate [typed witness route](guarded-witnesses.md) now binds conditional providers and canonical skipped slots through `Witness.compile`. External ledger, event and call effects retain their existing capability checks. Host-control plans emitted by `noctium_control` keep `nativeGuardQualified: false`; selecting that authoring route does not implicitly produce a native contract.

The circuit model has no shared temporary across separate outputs and constraints. Pure condition computations therefore repeat in host evaluation across those expressions. Native instruction sharing follows the existing compiler cache. Effectful condition evaluation is outside this slice.

The remaining state-aware helper bridge, private-state/witness scheduling and complete integrated prover/ledger requirements stay under [issue 43](https://github.com/awjreynolds/noctium/issues/43). This prerequisite slice is tracked in [issue 83](https://github.com/awjreynolds/noctium/issues/83). Finite iteration remains downstream in [issue 48](https://github.com/awjreynolds/noctium/issues/48).

## Focused evidence

The [native runtime case](../../runtime/tests/native_helper_branches.rs) uses the Source-generated plan and ZKIR. With an initial balance of 3, the active input `(true, 7)` returns 7 and writes 7. The inactive input `(false, 8)` returns 8, skips the failing assertion and cast, and preserves the exact initial state. Only the public input's two binding operations execute; the guarded state update does not execute. The active invalid input rejects during preparation. Altering the private guard in the native witness rejects at the checker.

Source guards cover early returns, lazy expression failures, lexical scope, unit assertions, aggregate results and private control rejection. Straight-line helper artifacts and an existing guarded-partial contract supply byte-comparison checks for the shared transformation.

The 71-job compiler/Claim build and the helper, control and component-disclosure checks pass. The native case passes in 0.01 seconds. Its relation contains 16 instructions, one public Native input, one private Bool input and one return binding. Three existing straight-line helper relations and the existing guarded-partial contract's relation/plan remain byte-identical. These counts do not measure K or proving time.

These checks do not establish whole-compiler preservation or full structured-effect equivalence. No new keys, proofs, deployments, K benchmark or portable SDK qualification accompanies this slice.
