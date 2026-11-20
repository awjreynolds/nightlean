# WebAssembly witness SDK for TypeScript

Noctium's browser package executes Lean-generated witnesses and produces locally verified Midnight call proofs in a dedicated Web Worker. It ships an ES module, TypeScript declarations and a WebAssembly module. The application owns provider calls and private storage. [Control ABI](../../runtime/include/noctium_control.h)

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

## Prove a ledger call

Use `AuthenticatedWitness` with the exact manifest bytes and its payloads in manifest order. Build the descriptor from independently trusted pins, including `abiVersion: 1`, `profile: "midnight-ledger-9-zkir-3.2.1"`, `trustedManifestSha256`, `proofParametersSha256`, `k` and `ttl` in Unix seconds. Source the digests independently of a server serving the bundle or SRS. The initial state uses `{"state":{...}}`. The begin envelope contains `abiVersion`, `inputs` and `hostContext`. The selected bundle supplies the witness plan. [Build an entrypoint bundle](portable-artifacts.md#build-and-use)

```ts
const witness = new AuthenticatedWitness(descriptor, manifest, payloads, srs, state, begin)
try {
    // Drive advance(), privateRequest() and resume(reply) with typed provider replies.
    // After the witness session reports completion:
    const proof = witness.prepareProof()
    try {
        const proved = await proof.proveLocally()
        try {
            const publicIntent = proved.publicIntent()
            // Return the public projection from the worker if the app needs it.
        } finally {
            proved.free()
        }
    } finally {
        proof.free()
    }
} finally {
    witness.free()
}
```

Preparing a proof consumes the completed witness session. The worker uses Web Crypto entropy, runs the native prover and verifies against the frozen statement. The public intent contains the commitment to the private binding value. To fund and submit the call, pass the proved object to the browser transaction client in the same worker.

## Reproduce the browser test

```sh
.lake/build/bin/noctium compile tests/WitnessSource.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit control --output build/web-witness-plans
cp sdk/web/tests/{browser-localnet.ts,witness-smoke.ts,witness-smoke.html} build/noctium-web/
cp build/web-witness-plans/TypedWitness.scalarHost.control.json build/noctium-web/plan.json
tsc --strict --target ES2022 --module ES2022 --moduleResolution bundler \
  --lib ES2022,ESNext.Disposable,WebWorker build/noctium-web/witness-smoke.ts
python3 -m http.server --bind 127.0.0.1 --directory build/noctium-web 8080
```

Open `/witness-smoke.html` on the loopback server. The page reports a passing result with five callbacks and result 14.

For the proof test, compile the same source with `--emit ledger --emit witness --emit control`. Assemble the `TypedWitness.ScalarWitness.claim` entrypoint with the pinned ZKIR 3.2.1 tool, ledger parameters and matching K7 keys. Place the bundle under `build/noctium-web/bundle/`, the public K7 proof parameters in `build/noctium-web/srs` and the pinned descriptor in `build/noctium-web/target.json`. Open `/witness-smoke.html?proof=1`. Use the published synthetic inputs from the test.

TypeScript 5.9.3 checked the generated declarations. Chrome 157.0.8103.79 produced and verified the K7 proof in 380 ms in one local worker run, excluding preparation and loading. The public projection was 4,126 bytes. The test rejected a modified control payload, a mismatched binding under recomputed fixture pins, a crossed callback reply and an incomplete witness. The separate control case checked cancellation and its input limit.

The size-optimized module measured 13,212,519 bytes raw and 2,158,023 bytes gzip-compressed. The same proof-enabled development build measured 36,549,903 bytes raw and 4,014,271 bytes gzipped. [TypeScript browser test](../../sdk/web/tests/witness-smoke.ts) · [Browser qualification ticket](https://github.com/awjreynolds/noctium/issues/90)


## Submit and recover a browser-proved call

Use `BrowserProvedCall.startCallClient(descriptor)` to transfer the proved call and
its source witness runtime into the native transaction driver. For a fresh
contract, use `startDeploymentClient(descriptor, setup)` first with a separate
deployment journal. The same driver handles native and browser attempts.

- Use `command()` and `poll()` to advance an attempt. Read the pending request
  with `request()` and reply with `complete(requestId, reply)`.
- Keep `privateRequest()` and `recoveryContext()` in the application's trusted
  storage and provider domain. Use `transactionRequest()` for the exact public
  submit or observe binding. Funding and sealing each require approval.
- Persist journal records with their expected revisions before acknowledging.
  After a worker restart, call `BrowserClient.recover(descriptor, context)`.
  The driver loads the stored attempt and validates the finalized receipt
  against the original contract, transaction and predicted state bytes before
  committing the staged private writes.

The localnet fixture uses IndexedDB for the journal and a separate loopback
Rust provider for the synthetic development wallet and chain. The browser
does not send journal or recovery data to the provider. The example requires
the isolated Ledger 9.1.0.1 development genesis and ZKIR 3.2.1.

### Run the localnet fixture

Prepare the same proof-enabled bundle, SRS, target descriptor and TypeScript
smoke test as above. Add `client.json` to the web folder.

```json
{
  "abiVersion": 1,
  "policy": {
    "networkId": "undeployed",
    "genesis": "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d",
    "specVersion": 2001100,
    "transactionVersion": 4,
    "profile": "midnight-ledger-9-zkir-3.2.1",
    "maxDust": "10000000000000000000000"
  },
  "capabilities": {
    "chain": "localnet",
    "funding": "development",
    "signing": "approval",
    "journal": "browser"
  }
}
```

Start the pinned development node from the [localnet guide](../../scripts/localnet/README.md).
Use a new chain for the smoke test. Set `NOCTIUM_LOCALNET_RPC` to its loopback
HTTP endpoint, `NOCTIUM_PARAMETERS` to the proving parameter cache and
`CHROME` to the Chrome executable.

```sh
cargo +1.100.0 build --locked --manifest-path runtime/Cargo.toml   --no-default-features --features zkir-321,localnet   --example browser_localnet_provider
python3 sdk/web/tests/run-localnet.py --web build/noctium-web   --provider runtime/target/debug/examples/browser_localnet_provider   --endpoint "$NOCTIUM_LOCALNET_RPC" --parameters "$NOCTIUM_PARAMETERS"   --chrome "$CHROME"
```
