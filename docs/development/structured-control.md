# Structured host control

Issue 42 adds lazy expressions, conditional statements and short-circuit
operators to the typed helper source model. Portable host execution uses the
Rust continuation machine and a separate C ABI. Node is unnecessary for source
compilation, callback execution and the C++ adapter.

Native proof and ledger lowering of general structured guards stays unavailable
until CF-02. The old eager scalar `select` keeps its existing semantics. Host
execution establishes no theorem about native guarded proof soundness.

## Bounded native write guards

Issue 43 now has a narrow source-to-checker slice for scalar state writes:

```lean
when disclose(enabled) write balance := nextBalance
when disclose(enabled) insert allowances[account] := amount
```

The compiler binds each write's Impact groups to the source guard. A private
guard must be disclosed because the active update changes the public ledger
transcript. The selected ZKIR 3.2.1 native checker accepts both active and
inactive cases and checks the full activity vector. The Rust materializer skips
inactive payload evaluation and state changes.

This slice supports guarded scalar cell and map writes only. Guarded reads and
guarded `require` effects fail validation. Guarded payloads with potentially
partial evaluation, including unsigned underflow, `assertThen`, and unsafe
narrowing casts, also fail validation until their native constraints use the
same activity guard. The selected-321 check lives in
`tests/Issue43ConditionalWrites.lean` and
`runtime/tests/conditional_writes.rs`.

Proof creation remains gated. The proof SDK still rejects skipped activity
groups until it binds post-proof `Noop` attachment, statement inputs, and gas
accounting to the checked schedule. This checker result does not close issue 43,
qualify a proof path, or cover general structured branches.

## Authoring and compilation

Use `Helpers.Term.ite`, `andThen`, `orElse` and `witness`, plus
`Helpers.Statement.branch` and `stage`. A witness names a registered provider
and declares its scalar result type. Staging names an explicit capability,
private-state key and scalar type. The complete working source is
[ControlSource.lean](../../tests/ControlSource.lean).

```lean
open scoped Nightlean
nightlean_control conditionalProviders from conditionalProvidersProgram
  entry "conditionalProviders"
```

The `nightlean_control` command checks the program and creates a registered
portable plan. The ordinary compiler exports this registry separately from
native circuits:

```sh
lake exe nightlean compile tests/ControlSource.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --output /private/tmp/nightlean-control-source
```

This source emits eleven `.control.json` files. `nightlean.json` lists their
filenames under `hostControlPlans` and records `nativeGuardQualified: false`.
Named calls refer to a typed function table. Exporting the plan never duplicates
callee subtrees. Declarations retain lexical identities, overload resolution,
argument order, scalar types and the implementation resource caps from
[named helpers](named-helpers.md).

Both arms receive type checks, even beneath a literal condition. Conditional
expression types require one arm to be a subtype of the other. Statements
allow discarded results with different types. Branch locals stay inside their
branch. A return exits the nearest named function. Purity analysis visits both
arms and the right operand of short-circuit expressions before scheduling.
`FN-PURE-INACTIVE` therefore rejects a declared-pure helper containing a witness
call inside a literal-false branch.

## Scheduling and host protocol

The host evaluates a condition before choosing one arm. `andThen` skips its
right operand after false. `orElse` skips its right operand after true.
Inactive assertions and narrowing casts do not execute or fail. The existing
`select` evaluates the condition and both values in order.

The portable runtime first validates the whole plan, including inactive
branches, function signatures, call cycles and resource limits. Execution uses
an explicit continuation stack. Suspension retains the current continuation.
Resuming a witness never replays earlier callbacks or private writes.

Every declared witness needs a registered provider, including witnesses which
remain inactive during the invocation. Providers use the existing versioned
host context, capability grants and typed schemas. A request binds its id,
operation, capability and scalar result schema. Invalid responses fail without
advancing execution. Cancellation invalidates pending requests and clears the
invocation's value buffers and private journal.

A source `stage` applies the existing host runtime's capability and typed-value
checks. Validated staged writes appear in the private request's
`invocationWrites` overlay for later callbacks. The original store remains
unchanged. Cancellation and failure clear the overlay and staged journal.
The control session exposes no transaction submission, receipt acceptance,
private-state CAS or durable commit operation. External side effects performed
inside arbitrary callback code receive no rollback guarantee.

Ordinary result transport carries host-execution statuses: ready, need-host,
completed, failed or cancelled. Scheduling and request metadata can depend on
private guards and remain visible to the host/controller. These messages are
not safe public contract observations or public logs. DF-00 checks successful
scalar contract-return payloads. It excludes host/provider activity and timing.
Execution errors use the fixed `execution_rejected` code.

Callback arguments, invocation writes and effect traces use separate private
accessors and private token handles. Ordinary result-copy functions reject
private tokens. This channel separation does not hide branch scheduling from
the host/controller.

## Disclosure

`Control.checkDisclosure` invokes the helper type, recursion, purity and hard
resource checks before its constant-aware DF-00 walk. Public inputs start with
no private origins. Private parameters and witness results retain their
origins through arithmetic, casts, hashing and helper calls.

Literal conditions select one arm for disclosure analysis. Unknown conditions
merge the origins of possible returned values. Statement conditions add a
separate accumulated control origin. Nested branches and early returns retain
this origin, including control over whether a later return executes.
Disclosing a returned payload does not release its surrounding statement guard.
Disclose the guard before branching to authorize that control dependence.
Unit returns have no public payload slot. They accept private control when no
public scalar value is returned. Scalar returns retain their control checks.
Assertions keep DF-00's current successful-execution scope. Their failure
behavior is not a general privacy guarantee.

The Rust runtime repeats type validation and checks actual returned origins
and control dependence before completing a successful scalar return. This does not make intermediate
host statuses confidential or safe to publish. These host checks do not
authorize guarded public ledger, event or cross-contract routes. Those routes
still need their source and native backend packages.

## Resource policy

All helper budgets remain immutable upper bounds. `WithLimits` APIs permit
only tighter budgets. Source preflight counts terms and statements in both
arms, including inactive and post-return syntax, before recursive passes.
Call-site multiplicity, memoized summaries, expanded-depth limits and shared
execution fuel remain active. Runtime continuation tasks and bounded abstract
constant/control analysis share the 131,072-step maximum. Abstract analysis
invokes no callbacks, stages no writes and changes no invocation state. The portable plan has a 1 MiB compact JSON limit. Emission reserves a
conservative byte allowance before constructing each node, including six bytes
per UTF-8 metadata byte for JSON escaping. `compileWithLimits` accepts an optional
fourth `maxPlanBytes` argument for tighter tests. Raising this allowance above
1 MiB fails. A minimal Unit plan exercises exact allowance boundaries of
1,072 bytes accepted and 1,071 rejected before construction.
Names and span filenames use at most 1,024 UTF-8 bytes. Lexical identity
components fit unsigned 64-bit integers, and span lines/columns stay at or below
1,000,000,000. These are local implementation caps, not language or ledger limits.
Oversized metadata errors never echo the rejected text. Witness names and stage capabilities/keys additionally
follow the existing host protocol syntax. At most 32 witness providers fit the
current host context. Host request, write and private-byte budgets remain
independent invocation limits.

## Evidence

Run `lake env lean tests/Control.lean` and
`lake env lean tests/ControlSource.lean`. Cases cover both-arm typing, subtype
joins, lazy assertions/casts, short-circuit order, eager-select distinction,
inactive purity, constant/private/nested control, payload-only disclosure,
authorized guards and private early returns. Existing named-helper and resource
boundary tests remain in `tests/Helpers.lean`.

The shared generated fixtures live in
[runtime/tests/fixtures/control](../../runtime/tests/fixtures/control).
The Rust callback driver and
[C++ C ABI driver](../../runtime/tests/control_cpp_smoke.cpp) consume the actual
Lean-generated `conditionalProviders` plan. The inactive case returns 7 with
zero callback invocations and zero staged writes. The active case invokes
`flag`, `left`, then `right`, stages one write between `left` and `right`, and
returns 22. The right callback observes `counter/value = 1` through the private
invocation overlay. Both adapters also reject the shared `activeFailure` plan
with the same fixed error and empty trace, and exercise cancellation.

```sh
cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321 --test control
```

Build the matching native library before compiling the C++ smoke program.
Link `runtime/tests/control_cpp_smoke.cpp` against `nightlean_runtime`, then pass
`conditionalProviders.control.json` and `activeFailure.control.json` as the two
arguments. The public ABI is documented in
[nightlean_control.h](../../runtime/include/nightlean_control.h). Fixture
callbacks and their values are public synthetic test data. Production callback
registrations and private inputs stay under the embedding host's control.
