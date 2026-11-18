# Native producer safety

Noctium now validates its emitted scalar ZKIR before returning an artifact from either public native lowerer. The compiler, descriptor registry, typed-statement normalizer and validator are Lean. No Compact compiler or runtime participates.

The registry follows the exact 47 instruction and 15 value-type inventory at native ZKIR revision `7a51b3385bbf4bce3604df87a7c70867c9ab43c0`. The producer emits IR version 3.2. The external native executable release, its source revision, ledger profile and host ABI remain separate identities.

## Supported extension contract

`Native.lean` records every instruction and value-type name in pinned enum order. Sixteen instruction descriptors support the current Native-scalar producer: Add, Mul, Neg, TestEq, Not, Assert, CondSelect, ConstrainBits, ConstrainEq, ConstrainToBoolean, LessThan, TransientHash, PublicInput, PrivateInput, Impact and Output. Only the native `Scalar<BLS12-381>` value representation is enabled. Noctium Bool and UInt values use constrained Native fields. Native `IrType::Bool`, bytes and all foreign-curve types remain unsupported here.

Each supported descriptor requires typing, encoding, privacy, effects, preconditions, guard policy, public-binding policy and exact field metadata. None has a default. A regression tactic verifies an omitted privacy/effect rule does not elaborate. Unknown instructions reject. Known unsupported inventory entries reject with an explicit implementation boundary. Registering a descriptor without an executable validation rule still rejects.

`NativeMeaning.lean` independently normalizes typed scalar expressions into symbolic field computations. `NativeExpected.lean` derives the input schema, ordered source assertions, returns, source range obligations and exact Impact group payloads from the validated, disclosure-checked typed program and native plan. This checks payloads and grouping rather than accepting a matching total field count. Input/read order, group boundaries and returned operands must agree. Required source assertions must occur in order, allowing intervening range assertions.

Symbolic equality is structural. An algebraic optimization needs its own preservation proof and a corresponding checked normalization change. This validator does not prove the entire lowerer correct or prove the native interpretation of the typed Impact plan.

## Executable checks

The validator checks exact JSON-AST fields, canonical minimal little-endian field immediates, Native type encodings, fresh SSA definitions and references before use. It tracks conservative upper bounds through Native arithmetic and explicit constraints. Assert, Not and selectors require an established Native 0/1 fact. LessThan requires both operands to fit its width before use. Supported widths are 1 through 248. Zero-width source integers use equality to zero.

Range obligations also cover declared Bool/UInt inputs and intermediate source expressions, including unused partial bindings retained by the frontend. An asserted bounded LessThan refines its referenced operand's upper bound. Missing input constraints, range assertions, source assertions, public groups or return bindings reject.

Exactly one final Output is mandatory. Standalone relations disable communications commitment and match their declared Native return signature. Ledger-call relations enable commitment and use an empty explicit return. Their exact typed Impact schedule supplies the public binding. This check does not authenticate runtime randomness, binding input, keys or an externally supplied ledger state.

PublicInput and PrivateInput accept only null guards in the current producer. Impact accepts only the literal active guard one. A preprocessing guard does not establish in-circuit activation, disclosure permission, lazy host execution or totality of inactive partial operations. Guarded source execution and unsupported partial primitives reject until their separate source and native packages are qualified.

Current caps are 4,096 instructions, 4,096 operands per vector, 512 transcript input definitions, 256 returns, 65,536 symbolic nodes per computed value and symbolic depth 256. These caps bound this producer check. They are not a complete source/elaboration/proving resource policy.

## Typed Bool plan repair

The generated native plan previously represented a public Bool parameter or Bool cell read as `Expr.ref name : Expr.native`, although its schema supplied a Bool. Honest Lean materialization then failed its reference type check. Both cases now use an explicit typed Bool-to-Native cast, matching the existing UInt bridge.

`Impact.Plan.validate` checks generated field and guard expressions against the source/output/read type environment before returning a plan. The regression test reconstructs the former mistyped Bool reference and requires rejection. False and true public-Bool/cell-Bool materialization cases pass. The cast erases to the same native field operand, so the corresponding ZKIR bytes stay unchanged.

## Safety requirement map

This map covers all 22 inventory requirements. A checked scalar rule is not a completion claim for the whole native target.

| Inventory requirement | Current evidence and remaining boundary |
| --- | --- |
| WELLFORMED | Executable SSA/reference and single-final-Output checks, malformed producer tests. Source-to-native preservation remains separate. |
| TYPECHECK | Exact current Native overloads and generated Impact field typing. Other 14 native value types and unsupported instructions fail closed. |
| BOOLEAN | Explicit abstract 0/1 preconditions for Assert, Not, selectors and guards. Native typed Bool is not enabled. |
| RANGES | Current UInt/scalar bounds and pre-use LessThan widths checked. Foreign conversions and inactive partial computations remain blocked. |
| GUARDEDINPUTS | Non-null input guards and nonconstant/false Impact guards reject. Structured guarded source execution and totalization remain unimplemented. |
| PUBLICBINDING | Exact symbolic public payload/group/read/return schedule checked against typed source/plan. Native ledger interpretation still depends on its separately tested codec and runtime. |
| DISCLOSURE | DF-00 runs before source/native lowering, and descriptors require privacy metadata. Broader native/function/composite privacy analysis remains open. |
| PRIVATEHOST | Outside this producer check. Provider capability, persistence, cancellation and accepted-outcome journal work belong to the native runtime track. |
| COMMITMENT | Header mode and return shape checked. Real randomness, call binding, key identity and encoded preimage agreement remain native assembly/verifier obligations. |
| CANONICAL | Strict current Native immediates and type representation. Runtime canonical witness decoding and future foreign/byte encodings remain separate obligations. |
| DEPENDENCIES | New compiler checks are Lean-only. Existing pinned native tools remain external dependencies. Compact stays absent from the execution dependency closure. |
| PROOFBOUNDARY | Raw checker observations and native keygen are reported separately below. Malicious internal-witness proving and complete verifier soundness remain open. |
| LEDGERTRANSCRIPT | Exact current typed payloads, activity groups and read ordering checked. Ledger codec semantics, actual costs and guaranteed/fallible partitioning remain separately qualified runtime obligations. |
| COMPOSITION | Cross-contract source/native composition remains unsupported and requires authenticated interface/key/entrypoint rules. |
| FAILURE | Ordered source assertions and scalar partial-expression checks retained. Structured partial failure, host outcomes and persistence remain separate packages. |
| LEDGERASSETS | No asset primitive is enabled by this registry. Conservation, ownership, authority and change require the asset implementation packages. |
| LIFECYCLE | Constructors, sealed state and maintenance/authority operations require native ledger lifecycle work. This gate does not qualify them. |
| RESOURCE | Current instruction/vector/symbolic/schema caps enforced. Whole-source, proving-memory and host/network budgets remain a wider policy. |
| SOURCEPROVENANCE | Registry drift test matches all 47/15 names to the pinned source inventory. Executable hashes, artifact authentication and deployed-key identity remain separate provenance checks. |
| FORMAT | Exact current producer JSON-AST schema and IR 3.2 checked. Tool release, ledger and host ABI versions remain independent and profile-validated. |
| HASHALIGNMENT | Only Native field-vector TransientHash is enabled. FAB byte alignment, option/compression segments and other hashes remain blocked. |
| MALICIOUSWITNESS | Raw out-of-range/wrong-statement tests exercise the official checker. This does not replace internal-witness or full native soundness proofs. |

## Qualification results

`tests/NativeProducer.lean` checks the complete inventory order/source pin and 65 positive/negative producer cases, plus the missing-metadata tactic and scoped Lean facts. It covers duplicate/missing SSA, exact fields/types, malformed/noncanonical constants, Assert Booleanity, ordering of constraints, LessThan widths, input guards, partial-op rejection, missing/reordered bindings and missing/reordered source assertions. It also executes the Bool materialization regressions.

The pinned official 3.2.1 checker and independently built native executable produced these observations:

- Assert of literal one passes the checker. Assert of literal two fails the checker, while key generation succeeds. Keygen success establishes geometry construction only. It does not establish a satisfying witness or proof.
- Two empty Output instructions pass the checker and keygen. A false assertion after Output still executes and rejects. The Lean producer rejects both malformed output structures.
- A guarded-off PrivateInput followed by inversion of its default zero still rejects. The input guard does not skip the following operation.
- A source public Bool accepts zero/one and rejects two or a changed bound return. Ranged LessThan rejects an out-of-range raw witness. An unbounded out-of-contract case also rejected in this checker run, without establishing a supported semantic contract.

No malicious internal-witness proof or new ledger transaction was produced for these raw observations. Full native soundness and verifier-boundary work remain open. The raw fixture runner deliberately bypasses the Lean gate to measure upstream behavior and is not an artifact-production route.

The accepted private-claim circuit retains SHA-256 `c569dd887fdf6aa3bdd2c8e2358985657ad3612eb72e0eb16f28682bb2b2b81c`. All 17 scalar artifact files remain byte-identical. The public Bool relation/cell relation also match a separately built pre-change compiler snapshot; only the formerly mistyped plan expressions require an intentional JSON cast change.

## Reproduce

```sh
lake build
lake env lean --run tests/NativeProducer.lean
.lake/build/bin/noctium compile tests/NativeProducerSource.lean --output /tmp/noctium-producer-bool
node tests/native-producer-checker.mjs "$OFFICIAL_321_CHECKER" /tmp/noctium-producer-bool "$NATIVE_321_CLI"
```

The optional native CLI argument enables the two raw keygen observations. JavaScript here is an official-library qualification harness. It implements no compiler pass or runtime semantics.

## Scoped facts and trust boundary

Lean proves that `requireBoolean` accepts exactly the tracked upper bounds at most one, that values below such an accurate bound are zero/one, and that the output-shape guard requires its executable single-final-output predicate. An unsupported descriptor cannot satisfy `requireInstruction`. Disclosure annotations preserve the normalized symbolic value and its range obligations.

These facts do not prove the abstract bounds sound for every native implementation or prove the normalizer preserves source semantics. They rely on audited native instruction behavior and the typed-source checks. The expected statement is derived by the public source lowerers after type/disclosure validation. A raw caller inventing an `Expected` record gains no source authorization, authenticity or complete compiler-correctness proof. Handwritten native artifacts remain a separate trust boundary.
