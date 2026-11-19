# WebAssembly witness SDK for TypeScript

Noctium's browser package runs Lean-generated host-control plans in the shared Rust runtime. It ships an ES module with TypeScript declarations and a WebAssembly module. The witness runs inside the browser, including in a dedicated Web Worker. The application owns provider calls and private storage. [Control ABI](../../runtime/include/noctium_control.h)

## Build the browser package

Install Rust 1.100.0, the matching `wasm32-unknown-unknown` target, wasm-bindgen CLI 0.2.130, Python 3 and LLVM's WebAssembly-capable `clang` and `llvm-ar`. Set `CC_wasm32_unknown_unknown` or `AR_wasm32_unknown_unknown` if those tools use different executable names. The build uses the same locked ZKIR 3.2.1 runtime as the mobile SDKs. [Rust target](https://doc.rust-lang.org/stable/rustc/platform-support/wasm32-unknown-unknown.html) · [wasm-bindgen web deployment](https://wasm-bindgen.github.io/wasm-bindgen/reference/deployment.html)

```sh
rustup target add --toolchain 1.100.0 wasm32-unknown-unknown
bash sdk/web/package.sh build/noctium-web
```

## Run a witness

Serve the generated files together. Pass the compiler's `--emit control` output with the invocation inputs and registered host capabilities in the version-one begin envelope.

```ts
import init, { WitnessSession } from "./noctium_witness.js"

await init()
const witness = new WitnessSession(new TextEncoder().encode(JSON.stringify(beginEnvelope)))
try {
    const step = witness.advance()
    // Dispatch each pending provider request and resume until completion.
} finally {
    witness.free()
}
```

The step data and replies are UTF-8 JSON in `Uint8Array` values. Read the separate private provider arguments and staged values through `privateRequest()`. Pass the exact correlated response to `resume(reply, true)` for a typed reply. Use `false` for a v1 reply. The adapter throws the numeric Control ABI status on rejection. `cancel()` invalidates a pending request. `close()` releases the native session, and `free()` releases the WebAssembly object. Keep private bytes and decoded provider data inside your trusted application.

## Reproduce the browser test

```sh
.lake/build/bin/noctium compile tests/WitnessSource.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit control --output build/web-witness-plans
cp sdk/web/tests/witness-smoke.{ts,html} build/noctium-web/
cp build/web-witness-plans/TypedWitness.scalarHost.control.json build/noctium-web/plan.json
tsc --strict --target ES2022 --module ES2022 --moduleResolution bundler \
  --lib ES2022,ESNext.Disposable,WebWorker build/noctium-web/witness-smoke.ts
python3 -m http.server --bind 127.0.0.1 --directory build/noctium-web 8080
```

Open `/witness-smoke.html` on the loopback server. The page reports a passing result with five callbacks and result 14.

TypeScript 5.9.3 checked the test against the generated declarations. Chrome 157.0.8103.79 completed it in a dedicated worker. The worker checked its private staged value, rejected a crossed reply without altering the pending request, checked cancellation, and rejected an oversized envelope. The measured WebAssembly file was 3,429,285 bytes. Browser bundle authentication, proving, wallet funding and transaction finality remain open. [TypeScript browser test](../../sdk/web/tests/witness-smoke.ts) · [Browser qualification ticket](https://github.com/awjreynolds/noctium/issues/90)
