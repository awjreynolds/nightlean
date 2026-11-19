# Swift witness SDK

Swift applications run Noctium host-control plans through the same Rust runtime as C and C++. The package links that runtime as a static XCFramework. It needs no Node process or Compact installation.

## Build and import

On Apple Silicon with Xcode, Swift 6 and the pinned Rust toolchain, install the Rust target for each platform you want. Then generate a Swift package with the same explicit target list.

```sh
rustup target add --toolchain 1.100.0 aarch64-apple-ios aarch64-apple-ios-sim
bash sdk/swift/package.sh build/noctium-swift \
  aarch64-apple-darwin aarch64-apple-ios aarch64-apple-ios-sim
```

Add the generated directory as a local Swift package in Xcode and link its `Noctium` product. Build only the slices you need. The package uses native ZKIR 3.2.1 and the repository's locked Rust dependencies. iOS compilation currently requires the compatible `libc` and `mio` patches recorded in `runtime/Cargo.lock`. The pinned ledger pulls in `sysinfo` 0.39, which imports an Apple network constant that `libc` 0.2.190 and later expose only on macOS. [Upstream sysinfo changelog](https://github.com/GuillaumeGomez/sysinfo/blob/main/CHANGELOG.md#0400) · [libc Apple declarations](https://github.com/rust-lang/libc/blob/0.2.190/src/unix/bsd/apple/mod.rs#L3706-L3743)

## Run a witness session

Compile a source `noctium_control` declaration with `--emit control`. Construct the Control ABI begin envelope with the emitted plan, your invocation inputs and your host capability registrations. `WitnessSession` takes the envelope as UTF-8 JSON `Data` and owns the native session until deinitialization.

```swift
import Foundation
import Noctium

let session = try WitnessSession(begin: beginEnvelope)
let step = try session.advance()
```

On `need_host`, call `privateRequest()`, run the registered provider, then pass the correlated reply to `resume(_:typed:)`. Use `typed: true` for the v2 reply format. Call `advance()` again until completion or rejection. `cancel()` invalidates the pending request. Keep step data, provider arguments, replies and staged values inside the trusted application. The Rust ABI frees each temporary result token before Swift returns its own copy. Your application owns any copies or logs it creates.

## Qualification

```sh
.lake/build/bin/noctium compile tests/WitnessSource.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit control --output build/swift-witness-plans
NOCTIUM_SWIFT_PLAN="$PWD/build/swift-witness-plans/TypedWitness.scalarHost.control.json" \
  swift test --package-path build/noctium-swift
```

The typed smoke case exercises five callbacks, reads a staged private value across callback boundaries, rejects a crossed attempt ID without advancing, and returns 14. It also checks that cancellation invalidates a pending private request. The same test passed on Apple Silicon macOS and the arm64 iOS 27.0 simulator. The arm64 iPhone slice linked with a minimum deployment target of iOS 16. Physical-device execution, proof generation, transaction submission and durable private-store commits remain open. [Swift smoke test](../../sdk/swift/Tests/NoctiumTests/WitnessSessionTests.swift) · [Control ABI](../../runtime/include/noctium_control.h)

To repeat the simulator test, run the package scheme against a booted simulator ID.

```sh
export TEST_RUNNER_NOCTIUM_SWIFT_PLAN="$PWD/build/swift-witness-plans/TypedWitness.scalarHost.control.json"
cd build/noctium-swift
xcodebuild test -scheme Noctium -destination "id=SIMULATOR_ID" \
  -parallel-testing-enabled NO -derivedDataPath ../swift-ios-test
```
