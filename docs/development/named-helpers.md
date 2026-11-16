# Typed named helpers

Issue 41 uses structured Lean source declarations, without a Compact dependency.
`Nightlean.Helpers.Program` contains lexical scopes, typed named declarations and
monomorphic exports. `nightlean_helper_circuit name from program entry "export"`
checks and registers an export in the existing frontend. Existing
`nightlean_contract` entries then use the resulting circuit normally.

See [the complete source example](../../tests/HelperSource.lean). Its `relation`
helper calls a forward-declared `square`, checks the result against a public
parameter and returns the public parameter. `helperComposed` and `helperDirect`
express the same scalar relation. `HelperContract` uses the composed relation
with a native state-cell write.

```lean
import Nightlean.Frontend
open Nightlean.Helpers

def arithmeticHelpers : Program := {
  declarations := [{
    id := ⟨0, 0⟩
    name := "double"
    parameters := [⟨"x", .native⟩]
    result := .scalar .native
    declaredPure := true
    body := [.return (some (.binary .add (.ref "x") (.ref "x")))]
  }]
  exports := [{
    name := "double"
    target := ⟨0, 0⟩
    inputs := [{name := "x", ty := .native, visibility := .public}]
  }]
}

open scoped Nightlean
nightlean_helper_circuit doubleRelation from arithmeticHelpers entry "double"
```

Declare structured programs before opening the Nightlean syntax scope, or use
`Bool.true` and `Bool.false` for Lean Boolean fields. The scope reserves source
keywords such as `true`, `false` and `output`.

## Checking and execution

A declaration has a lexical identity `(scope, ordinal)`. Names identify overload
sets, not declarations. A scope has an optional parent. Calls search compatible
signatures within one scope before visiting its parent. An inner compatible
candidate wins even when an outer declaration also matches. Multiple compatible
candidates in the first matching scope fail, without choosing the narrowest
signature. A value binding blocks lookup through its scope. Argument types use
scalar widening rules. Explicit casts perform checked narrowing.

Every declaration signature and statement receives static checks. Reachable
call-graph cycles fail before lowering. Unreachable recursive declarations are
excluded from recursion and purity analysis. Bodies retain checks after an
explicit return. This is a deliberate diagnostic difference from pruning all
unused syntax before type checking.

Parameters and results have declared types. Statements support typed local
bindings, discarded expressions, assertions and returns. Falling through, or
returning without a value, produces unit. A scalar result therefore requires a
compatible explicit return. Unit is separate from scalar `Ty` and never becomes a
public result slot.

Calls lower to ordered scalar `Expr.letE` bindings with fresh names. Actual
arguments evaluate left to right once, then the body evaluates. Unused arguments
still evaluate. The same rule retains unused failing casts and assertions.
`Expr.assertE` preserves assertion order inside the body. The Lean evaluator,
native producer, Rust runtime and emitted native-plan expression format share
these sequencing rules. Locals preserve Boolean and bounded-unsigned types.
Bindings restore the enclosing environment on exit.

## Effects and disclosure

Transitive summaries distinguish witness access, private-state access, ledger
reads, ledger writes, assertions, fallible casts, events and cross-contract
calls. Assertions and fallible scalar casts are permitted in pure helpers.
Witness/private-state access, ledger access, events and cross-contract calls
make a helper impure, including through another helper. Declared purity checks
all statement syntax before lowering. `FN-PURE-INACTIVE` remains registered for
CF-01, which introduces structured branch syntax. Existing eager `select`
checks and evaluates both operands.

External effects currently lack helper backend implementations. Compilation
returns a named native capability error. `Helpers.trace` evaluates explicit
labelled effect fixtures to test ordering. These fixtures supply results and
record labels. They invoke no witness callbacks or external effects and do not
claim backend support.

Compilation invokes mandatory DF-00 after call lowering. A parameter receives
the actual argument's private origins through its local binding. Arithmetic,
casts, hashing and further calls retain those origins. Explicit `disclose`
clears only the wrapped value's origins. Assertion arguments are checked for
valid origins, but assertion success/failure is outside DF-00's current
successful-execution disclosure claim. Helpers add no disclosure exemption.

This package supports scalar parameters/results and unit. Composite execution,
component-level disclosure, branch execution, anonymous operators and generics
belong to their separate feature tickets.

## Compiler resource policy

`Helpers.Limits` defines local implementation caps. These are not Compact
language limits. Existing `compile`, `analyze`, `infer`, `resolve`,
`checkDeclaration` and `trace` APIs apply the defaults. Their `WithLimits`
variants accept stricter budgets for embedding and small-budget tests.
Every supplied field must stay at or below the immutable implementation policy.
Raised budgets fail before any program traversal.

The defaults allow 256 declarations, scopes and exports, 64 parameters,
arguments, exported inputs or value bindings per scope, and 16,384 total source
statement/term nodes. Source term nesting is limited to 128. A bounded work-list
preflight checks source size and depth before recursive type analysis.

Reachable call depth is limited to 64. Memoized call-graph analysis allows
65,536 visits, including cache hits. Summaries retain repeated call sites when
counting expansion. Each declaration contributes a conservative node allowance
of three times its statement count, term count, parameter count and two wrapper
nodes. Each call site adds its callee's allowance, including repeated calls to
the same declaration. Addition saturates at the configured cap plus one.
The corresponding conservative depth bound adds each declaration's allowance
for statements, maximum term depth, parameters and wrappers along the longest
callee path. Defaults cap expanded nodes at 65,536 and depth at 256.
These checks run before constructing inlined expressions. They include syntax
after a return and therefore sometimes reject more than a runtime-only count.

Lowering and trace evaluation each receive a separate shared budget of 131,072
steps. Every term, body continuation, call and parameter consumes fuel before
execution or construction. Call-resolution and public raw-program entrypoints
also receive source preflight checks. Resource failures return diagnostics.
They do not discard arguments, skip checks or weaken disclosure.

The regression fixture with 13 declarations and two calls per non-leaf
function fails before its exponential expression tree is built. A two-function
fixture exercises exact boundaries of 30 conservative expanded nodes, depth 21,
three memoized graph visits and ten execution steps. Its next smaller limits
fail. A ten-level DAG requires 21 graph visits, demonstrating cache reuse.

## Evidence

Run `lake env lean tests/Helpers.lean` and
`lake env lean tests/HelperSource.lean`. The cases cover `FN-ARGS-ORDER`,
`FN-RETURN-UNIT`, the three overload cases, direct and mutual recursion,
`FN-PURE-INDIRECT` and scalar `DISC-HELPER`. Extra cases cover hidden function
bindings, unreachable recursion, source-wide purity, capability errors, fresh
binding capture avoidance, unused failing arguments, unique export/declaration
identities and missing nested native assertions.

`runtime/tests/helpers.rs` checks native local binding scope, scalar type
preservation, assertion order and unused argument failure. Native checker/prover
qualification for the composed/direct source pair lives in
[the helper qualification runner](../../tests/helpers/qualify.mjs). Its output
records acceptance and rejection evidence separately from Lean unit checks.


The tracked [qualification evidence](../../tests/helpers/qualification-evidence.json)
records identical direct/helper JSON and binary relations at k=4 with ten rows.
For each relation, the pinned 3.2.1 checker accepted valid and zero cases and
rejected wrong secrets, public inputs and public outputs. The native proof
service generated and self-verified a 3,468-byte proof for each relation.
These are scalar fixture results, separate from general compiler preservation
or ledger correspondence proofs.

The qualification parameter cache lacked k=4 parameters. The fixture used the
pinned library's `ParamsKZG::downsize(4)` on an existing official k=5 file.
The public preparation utility checks the parent SHA-256, decodes the parent
parameters and refuses to replace a different existing output. Reproduce this
step against the same cache with:

```sh
cargo +1.100.0 run --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321 \
  --example qualify_helper_parameters -- \
  /private/tmp/nightlean-proof-params/bls_midnight_2p5 \
  /private/tmp/nightlean-proof-params/bls_midnight_2p4
```

The 6,532-byte parent SHA-256 is
`0a1c9229f315fc1868ff25f668fb83aec4d09f4f23a706b5197c692c619d72c6`.
The derived 3,460-byte k=4 SHA-256 is
`232f401fad10c7ddf8828d2aa4c85c6506c5da09795998cecaeb9f75fc8f6ada`.
This is fixture parameter preparation, not a new trusted ceremony. Trust in
the parent ceremony stays external.

Regenerate source artifacts through the matching target:

```sh
lake exe nightlean compile tests/HelperSource.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output /private/tmp/nightlean-helper-source-321
```

Generate the relation keys with the pinned 3.2.1 tool and the prepared parameter
cache. Run `node tests/helpers/qualify.mjs DIRECTORY PINNED_CHECKER_MODULE check`
for checker cases, or replace `check` with `prove` after key generation.
Proof mode uses the local proof service at `http://127.0.0.1:16300` by default.
`NIGHTLEAN_PROOF_SERVER` selects another loopback service. The qualification
service used `/private/tmp/nightlean-proof-params` as its host parameter cache.
See the [matching native profile instructions](zkir-3.2.1-integrated.md) for
profile and tool identity requirements.
