# Portable witness execution: Noir, Aztec, Circom, and Nightlean

Research checked on 2026-11-16. This report separates verified implementation facts from architectural recommendations. No runtime was built or benchmarked for this research.

## Recommendation

Keep Lean 4 as the compiler. Give the compiler-owned witness/execution plan a versioned, host-neutral format and implement one resumable execution core, preferably in Rust. Ship this core as a native library and as WebAssembly. Put storage, keys, network access, entropy, and user interaction behind an explicit provider protocol. Keep circuit proving behind a separate adapter.

For Nightlean's present plan, a small interpreter for the compiler-owned plan is the lowest-risk starting point. Native Rust, a C ABI, Android JNI, and Swift bindings would share the implementation. A browser would run its WASM build. This avoids implementing the same field arithmetic, transcript serialization, and plan semantics in each host language.

Per-program WASM is a valid later target, especially for general application-supplied computations or distributing one executable witness artifact. Require the same provider protocol and bounded execution contract. Do not make a direct Lean-to-WASM compiler backend, a general WASM runtime in every native application, or a new proving VM prerequisites for removing Node.

This is a recommendation derived from the comparisons below, not an existing Nightlean implementation or a claim about measured performance.

## Separate the responsibilities

Use three distinct interfaces:

1. A witness provider supplies values from wallet storage, APIs, user input, keys, or randomness. Its values are external inputs. A provider might be entirely native Kotlin or Swift.
2. A deterministic execution core evaluates the emitted plan, validates typed inputs, requests external values, computes local outputs, and constructs the private/public transcript material required by the backend. Replaying the same program, initial state snapshot, and provider responses should reproduce the same result.
3. A circuit executor/prover fills circuit intermediates and produces the proof. Its constraints establish correctness of the claimed relation. Successful witness execution does not establish correctness by itself.

The local helper currently combines several responsibilities. `evaluate` computes emitted expressions, `environment` loads inputs and derives outputs, `materialize` constructs Impact operations and private outputs, and `callPrototype` calls ledger APIs for commitments, transcript partitioning, and the call prototype. These functions import `@midnight-ntwrk/ledger-v9`. Replacing only application witness callbacks would leave this JavaScript dependency in place. [Current helper](../../scripts/zkir/native-runtime.mjs)

The separate ZKIR backend already has responsibility for circuit execution and intermediate witnesses. A portable application execution core should not duplicate the entire proving backend. The existing witness/state research records the backend boundary and confidentiality implications of proof-server inputs. [Existing boundary research](midnight-witness-state-model.md)

## Verified comparison: Noir

Source pin: `noir-lang/noir` commit `e5a1160aa6dea59567a95f382a366e72dd0ffa86`.

Noir's `acvm` is a native Rust crate depending on ACIR, `brillig_vm`, and black-box solvers. Its manifest does not depend on the JavaScript wrapper. The interpreter consumes ACIR operations and a witness map, with Brillig bytecode for unconstrained functions. This gives a real native implementation to embed, rather than requiring a WASM package to stand in for a native API. [ACVM manifest](https://github.com/noir-lang/noir/blob/e5a1160aa6dea59567a95f382a366e72dd0ffa86/acvm-repo/acvm/Cargo.toml)

`ACVMStatus` distinguishes solved, in progress, failure, foreign-call request, and ACIR-call request. The VM exposes pending foreign-call information and `resolve_pending_foreign_call`, so an embedder obtains the request, resolves the external work, supplies the response, and resumes execution. This is an explicit suspension boundary independent of a JavaScript event loop. [ACVM execution state](https://github.com/noir-lang/noir/blob/e5a1160aa6dea59567a95f382a366e72dd0ffa86/acvm-repo/acvm/src/pwg/mod.rs)

Brillig implements general unconstrained computation and foreign calls. Its documentation describes a finite-field VM, memory, control flow, and externally supplied results. This illustrates an important distinction: unconstrained execution computes candidate values, while circuit constraints establish the properties required of those values. Brillig execution itself is not automatically proven when used as an unconstrained ACIR helper. [Brillig documentation](https://noir-lang.github.io/noir/docs/brillig/index.html)

The separate `acvm_js` implementation uses `wasm_bindgen`, JavaScript witness-map types, and asynchronous exported functions. Its execution loop awaits a JavaScript foreign-call handler, then feeds the result back to the Rust VM. Therefore the distributed JS-facing WASM wrapper is not evidence of a standalone WASI module or a host-independent import ABI. A native host would embed the Rust core or need a different wrapper. [JS/WASM execution wrapper](https://github.com/noir-lang/noir/blob/e5a1160aa6dea59567a95f382a366e72dd0ffa86/acvm-repo/acvm_js/src/execute.rs)

Lesson for Nightlean: copy the separation between program format, deterministic executor, foreign-call protocol, and language wrapper. Adopting Noir or Brillig as Nightlean's compiler backend is not necessary. This inspection establishes Rust embedding and the JS/WASM wrapper, not an official supported ACVM SDK for all of C++, Kotlin, and Swift.

## Verified comparison: Aztec

Aztec's current documentation describes PXE as a TypeScript client library usable in Node, wallet software, or a browser. PXE stores private data and keys, synchronizes relevant state, implements oracles, and orchestrates execution and proof generation. Browser execution removes a Node requirement for that deployment, but retains a JavaScript runtime. [PXE architecture](https://docs.aztec.network/developers/docs/foundational-topics/pxe)

The oracle documentation describes fetching private notes and membership paths through PXE. Returned values are unconstrained and require circuit checks. This separates the provider's knowledge and local storage from the circuit's acceptance conditions. [Protocol oracles](https://docs.aztec.network/developers/v5.2.0/docs/aztec-nr/framework-description/advanced/protocol_oracles)

The inspected `aztec-packages` commit is `e5a1cbe62b51ed89cf30047ffd03be786cfdb72a`. Its `labs` submodule points to `aztec-labs-eng/aztec-node` commit `677343f0ea25c0b20b60a648cbf80e8207dfec13`. The following implementation findings use this pinned submodule, rather than assuming old `yarn-project` URLs still refer to current source. [Submodule declaration](https://github.com/AztecProtocol/aztec-packages/blob/e5a1cbe62b51ed89cf30047ffd03be786cfdb72a/.gitmodules) [Pinned submodule](https://github.com/aztec-labs-eng/aztec-node/tree/677343f0ea25c0b20b60a648cbf80e8207dfec13)

`WASMSimulator` imports ACVM and ABI functions from the Noir JS packages. It initializes browser WASM modules, encodes inputs, and executes user circuits through a TypeScript wrapper. That wrapper dispatches oracle names to callbacks returning promises. The application provider layer is still TypeScript. [WASM simulator](https://github.com/aztec-labs-eng/aztec-node/blob/677343f0ea25c0b20b60a648cbf80e8207dfec13/yarn-project/simulator/src/private/acvm_wasm.ts) [Oracle dispatch](https://github.com/aztec-labs-eng/aztec-node/blob/677343f0ea25c0b20b60a648cbf80e8207dfec13/yarn-project/simulator/src/private/acvm/acvm.ts)

`NativeACVMSimulator` imports `child_process`, `fs`, and `node:crypto`. It launches `noir-execute`, exchanges artifacts/inputs/witness files, rejects foreign-call callbacks, and throws `Not implemented` for `executeUserCircuit`. This is native acceleration of supported protocol execution inside Node orchestration. It does not establish a native PXE or a native user-circuit path with wallet oracles. [Native simulator](https://github.com/aztec-labs-eng/aztec-node/blob/677343f0ea25c0b20b60a648cbf80e8207dfec13/yarn-project/simulator/src/private/acvm_native.ts)

PXE's package exports JavaScript entry points and depends on `bb.js`, Noir JS packages, the simulator, a key store, and a KV store. Its manifest declares Node `>=24`, although the distinct client entries support browser packaging. Neither the manifest nor the inspected simulator source establishes a ready-made Rust/C++/Kotlin/Swift PXE. [PXE package](https://github.com/aztec-labs-eng/aztec-node/blob/677343f0ea25c0b20b60a648cbf80e8207dfec13/yarn-project/pxe/package.json)

Lesson for Nightlean: adopt the separation of private-state providers, oracle ABI, execution, and proving. Do not treat Aztec's WASM internals or native protocol simulator as proof of a language-neutral wallet stack. Aztec's oracle versioning is also a useful precedent for explicit compatibility between compiled programs and host capabilities. [Oracle versioning](https://docs.aztec.network/developers/docs/foundational-topics/pxe#oracle-versioning)

## Verified comparison: Circom

Circom documents two generated witness calculators: WASM and C++. Both compute signal values from supplied inputs before the proving step. The C++ output includes source and a Makefile, demonstrating a direct native route without making Node the witness-execution runtime. This is narrower than a wallet provider/oracle system. [Witness calculation](https://docs.circom.io/getting-started/computing-the-witness/)

At commit `9b4b23331644e17868c90a85768826ed3bcba59f`, the WASM calculator wrapper instantiates a module with imports under `runtime` for error/log handling. It feeds field limbs and signal identifiers through exports, reads witness values, and serializes WTNS. The generated launcher uses Node `fs` and process arguments. A different embedder would need to implement this import/export and data-layout contract rather than run the launcher unchanged. [Calculator wrapper](https://github.com/iden3/circom/blob/9b4b23331644e17868c90a85768826ed3bcba59f/code_producers/src/wasm_elements/common/witness_calculator.js) [Node launcher](https://github.com/iden3/circom/blob/9b4b23331644e17868c90a85768826ed3bcba59f/code_producers/src/wasm_elements/common/generate_witness.js)

Lesson for Nightlean: portable computation still needs an ABI and artifact format. WASM alone does not specify field encoding, schema validation, witness serialization, storage, or host capabilities. Generated C++ is another valid route, with a separate per-program native build/distribution burden.

## Native embeddings and mobile constraints

| Host | Practical Nightlean route, recommended | Verified runtime precedent and limits |
| --- | --- | --- |
| Rust | Link the execution-core crate directly. Use WASM interpretation for separately supplied guest code if needed. | Noir has a native Rust ACVM. Wasmi supplies a Rust interpreter with fuel metering and a C API. |
| C++ | Call a small C ABI over the same core, with opaque handles and owned byte buffers. | Wasmtime has a C API and a C++ asynchronous-host-function example. Wasmi implements the Wasm C API. |
| Kotlin/Android | Call the native core through a narrow JNI layer. Keep coroutine scheduling, secure storage, and networking in Kotlin. | Android documents JNI interoperability for Kotlin and Java. Nightlean-specific JNI packaging still needs implementation and device tests. |
| Swift/iOS | Link a native library through a C interface, or embed an interpreter for portable WASM programs. Keep provider work in Swift tasks. | WasmKit is an embeddable Swift runtime. Its pinned README lists iOS 18+ as expected to work, but lists continuous testing on macOS, Linux, Android, and Windows, not iOS. |

Wasmi's inspected commit `d6188fb1835a8fbfcb2208e00ff7c2c5d5de1392` documents interpretation, fuel metering, `no_std` operation, and the C API. Its feature matrix lists threads, GC, and exception handling as planned rather than implemented. This is a plausible conservative runtime for scalar witness programs, not a claim of a validated Nightlean mobile SDK. [Wasmi](https://github.com/wasmi-labs/wasmi/blob/d6188fb1835a8fbfcb2208e00ff7c2c5d5de1392/README.md)

WasmKit commit `6558e71635384e4c7e371297a30656b89dd2682c` documents an embeddable Swift library, an engine without external package dependencies, and a component model still in progress. The inspected branch requires Swift 6.3. These requirements need a release choice matched to Nightlean's supported iOS versions. [WasmKit](https://github.com/swiftwasm/WasmKit/blob/6558e71635384e4c7e371297a30656b89dd2682c/README.md)

Wasmtime documents desktop OSes as its primary support, with Android and iOS supported but less tested. Its Cranelift/Winch modes require creating executable memory pages, including when loading AOT output. Therefore AOT alone does not establish a suitable iOS deployment route. [Platform support](https://docs.wasmtime.dev/stability-platform-support.html)

Pulley provides an interpreter route through Wasmtime's existing Rust and C APIs. Its bytecode depends on pointer width, endianness, and Wasmtime version. Treat a precompiled Pulley artifact as an engine-specific cache, not Nightlean's portable canonical artifact. Its documentation expects slower execution than native compiled code. No Nightlean workload was measured. [Pulley](https://docs.wasmtime.dev/examples-pulley.html)

Apple documents restrictions on writable/executable memory and dynamic code-signing entitlements. For ordinary iOS application design, choose a non-JIT interpreter for dynamic programs or statically linked native code for fixed runtime components. This is an engineering recommendation, not a completed App Store policy review. [Apple runtime security](https://support.apple.com/en-ie/guide/security-pdf/sec15bfe098e/1/web/1)

Android recommends minimizing JNI marshalling and avoiding complicated asynchronous communication across JNI. A coarse `advance`/`resume` boundary keeps asynchronous provider work in Kotlin and transfers typed batches of data. [Android JNI guidance](https://developer.android.com/ndk/guides/jni-tips)

## Recommended execution contract

Define a logical state machine shared by native and WASM builds:

```text
start(program, typed_inputs, state_snapshot, execution_limits) -> session
advance(session) -> Done(result) | NeedHost(request) | Failed(error)
resume(session, request_id, typed_response) -> status
cancel(session)
free(session)
```

The session owns continuation state. `NeedHost` includes a declared operation identifier, version, request ID, arguments, and expected result type. The host performs I/O, then resumes. A first implementation should support one outstanding request per session. Batching is an explicit later ABI feature.

This design is an inference from Noir's suspend/resume model. An async language adapter awaits providers outside the executor. A synchronous C API stays synchronous. No language adapter needs to retain an unmanaged callback stack across an `await`. Wasmtime does offer asynchronous host functions, but those are engine APIs, not a portable promise ABI shared by every WASM embedder. [Wasmtime async example](https://docs.wasmtime.dev/examples-async.html)

Recommended v1 requirements:

- Specify canonical bytes for fields, integers, booleans, arrays, and transcripts. Reject malformed or out-of-range values before evaluation.
- Pin program-format version, ABI version, backend profile, arithmetic/hash semantics, and required provider capabilities in the artifact manifest.
- Give the executor no ambient filesystem, network, clock, or entropy imports. Expose only declared capabilities. Feed randomness explicitly and retain replay data only under the wallet's secret-handling rules.
- Return proposed local state changes as an effect journal. Let the host commit changes under the transaction lifecycle, with defined cancellation and failure behavior.
- Bound instruction work, memory, host requests, and result sizes. Specify cancellation and error codes across all bindings.
- For WASM v1, use explicit memory buffers and a small scalar core ABI. Do not require WASI, WASM GC, threads, or the component model merely to run witness logic.

Do not promise cross-process serialization of suspended sessions in v1. Opaque in-process handles are sufficient for async provider calls and avoid making interpreter memory layout part of the compatibility contract.

## What needs evidence before implementation selection

The architecture removes mandatory Node only after every execution dependency crosses the new boundary. The present ledger-v9 calls require a native implementation, a host-independent WASM interface, or a carefully scoped backend adapter. A Node-backed adapter would leave the portability objective incomplete.

Resolve these gaps with one bounded prototype before selecting packaging:

1. Run one emitted plan and a mocked provider through the shared core in native Rust and standalone WASM. Compare typed outputs and transcript bytes against the current helper.
2. Exercise suspension, cancellation, provider rejection, malformed input, execution limits, and state-effect rollback. Do not limit the trial to arithmetic without host requests.
3. Embed on Android and an iOS device without Node or a JavaScript engine. Measure startup, peak memory, host-boundary copying, and witness computation separately from proving.
4. Inventory ledger-v9 hashing, alignment, state operations, transcript partitioning, and prototype construction. Establish the supported non-JS route for each call.
5. Confirm the ZKIR/proving adapter remains the sole owner of circuit intermediates and accepts the portable executor's output unchanged.

No checked source establishes an off-the-shelf Noir or Aztec native wallet stack spanning all four requested host languages. The evidence supports shared portable computation with explicit provider bindings. Nightlean still needs its own ABI, compatibility tests, and mobile packaging.
