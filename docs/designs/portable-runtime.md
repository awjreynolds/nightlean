# Portable runtime and witness execution

Status: implementation direction for the feature-equivalence goal. The native Rust probe is in progress. No mobile SDK or portable WASM runtime is qualified yet.

## Required boundary

The compiler remains Lean 4 and emits ZKIR and a versioned execution plan. Applications choose their host language. Neither witness execution nor native transaction construction requires a Node subprocess in the target architecture. The current JavaScript helpers remain a measured conformance reference until their native replacement passes equivalent checks.

Three terms have distinct meanings:

- A witness is private input data supplied to a circuit.
- A witness provider obtains data or performs application work, such as reading wallet storage or requesting a signature. The host application owns its permissions and implementation language.
- Circuit witness generation computes constrained intermediate values inside the selected proving backend. It is separate from application providers and from ledger transaction orchestration.

The present JavaScript helper performs more than provider calls: it evaluates compiler expressions, builds native state operations, partitions transcripts, and assembles a call. Replacing only a callback would leave a JavaScript dependency in the execution path.

## Shared execution core

Implement one reference runtime in Rust over the compiler-owned plan and official Midnight native libraries. Native Rust callers link it directly. C and C++ use a narrow C ABI. Kotlin and Swift receive native bindings over the same core. Browser and optional JavaScript hosts use a WASM build with TypeScript declarations and wrappers.

This is a runtime implementation choice, not a change to the compiler implementation language. A Rust application must not have to embed a JavaScript engine. A native application also need not embed a WASM engine merely to execute the standard Nightlean plan.

The ABI is defined independently from any binding generator. Canonical buffers and explicit ownership cross the boundary. Field elements use the named target profile's canonical representation, rather than JavaScript numbers or a platform-dependent integer ABI. Errors, limits, cancellation, memory ownership, and execution capabilities are versioned parts of the contract.

## Provider requests

Use an explicit resumable protocol rather than retaining a foreign callback stack across asynchronous work:

```text
start(bundle, inputs, state_snapshot, limits) -> session
advance(session) -> completed(result) | need_host(request) | failed(error)
resume(session, request_id, typed_response) -> status
cancel(session)
release(session)
```

Each request names a versioned provider operation, arguments, expected result schema, and capability scope. The host resolves storage, network, keys, entropy, and user interaction in its own language. Returned values remain untrusted and receive type/range validation. Circuit constraints establish the properties needed by the proved statement.

The executor has no ambient access to files, network, wallet keys, or system time. Private-state writes return as a proposed journal. The host commits or rejects the journal according to the transaction outcome. Cancellation, stale state, retries, and uncertain submission outcomes must not silently commit private state.

## WASM role

WASM is a supported packaging direction, not the definition of the witness API. The same Rust execution core should have native and WASM builds where dependencies support them. Application-supplied portable witness computations may later be delivered as separate WASM modules using the same provider protocol.

The first portability ABI should not require WASI, JavaScript imports, threads, garbage collection, or a particular component runtime. Mobile execution needs actual target builds and device checks. A WASM module alone does not settle iOS executable-memory restrictions, asynchronous host calls, secret handling, or proof-generation resources.

## Artifact stages

| Stage | Outputs | Ownership |
| --- | --- | --- |
| Lean compilation | ZKIR, execution plan, input/output/provider schemas, state schema, source diagnostics/maps | Lean compiler |
| Target key generation | Proving key, verifying key, binary relation, parameter and toolchain provenance | Pinned native Midnight tools |
| Bundle assembly | Versioned manifest linking source, circuit, plan, schemas, keys, target profile and content digests | Reproducible packaging step |
| SDK generation | Rust API types, C headers, Kotlin/Swift bindings, optional TypeScript bindings | Shared schema and runtime ABI |
| Optional portable code generation | Runtime WASM and, where needed, application witness WASM | Separate qualified target |
| Execution | Private inputs, provider responses, local state journals, proofs and transactions | Application and runtime, outside the public bundle |

The public bundle contains programs, schemas and public artifacts. Runtime witness values, wallet secrets, and private application storage do not belong in that bundle. Rebuilding keys and distributing a bundle are distinct stages from source compilation, and their provenance must remain explicit.

## First implementation gate

Run the existing actual-source private claim in a Rust process without invoking Node for expression evaluation, private transcript packing, Impact execution, transcript budgeting, or proof-preimage construction. Pin and unify the official Rust dependency graph. Match canonical values and transcript behavior against the already qualified conformance vectors. Wrong witnesses and replay must fail without state mutation.

Only after this gate should the ABI be frozen and C/C++, WASM, Kotlin, Swift, and TypeScript bindings be qualified. Native prover embedding and local/remote proof-provider choices need their own resource and privacy tests. The initial Rust probe does not by itself qualify the complete wallet or SDK.

## Research basis

- [Runtime boundaries and pinned Midnight APIs](../research/nightlean-portable-runtime-boundary.md)
- [Noir, Aztec, Circom and mobile runtime comparison](../research/portable-witness-comparison.md)

These reports distinguish verified upstream APIs from Nightlean recommendations and untested target support.
