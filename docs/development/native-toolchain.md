# Independent native ZKIR toolchain

Nightlean's supported key-generation path uses the independent `midnightntwrk/midnight-zkir` project. The source-language compiler is unnecessary for this path. Nightlean's own compiler and lowering remain Lean code. The external native ZKIR CLI generates proving and verifying keys from the emitted relation.

## Verified build

On 2026-11-16, the native CLI built and generated claim keys on macOS ARM64 using:

| Input | Pin |
| --- | --- |
| Upstream source | [`446c7fecc6bd41dab99ebe89ab404e9d077d11a9`](https://github.com/midnightntwrk/midnight-zkir/tree/446c7fecc6bd41dab99ebe89ab404e9d077d11a9) |
| Release | `zkir-3.2.0` |
| Rust | `1.100.0`, commit `0ef1bc386`, host `aarch64-apple-darwin` |
| Cargo lock SHA-256 | `82e40bec16af677a2b42b291e5034ab01944f40dee6c5d2afe8a5b0199beacf1` |
| Built binary SHA-256 | `2664d4d6f97c04e882b4208b9926f27f1e1d03082ca508e69f0145c491aa694a` |
| CLI version output | `midnight-zkir 3.2.0` |

The untouched upstream workspace built in 1 minute 48 seconds with four jobs. Cargo used the checked-in lockfile and its pinned ledger dependency revision `9a8777c4d035fc7f38ae286bcf5f8656668efd9f`. The binary hash records this host's build output. It is not a promise of byte-identical output across different hosts or native toolchains.

## Reproduce

Install Rust 1.100.0 and a native C build toolchain. The verified host had Xcode's Apple Clang 21 and CMake available. Then run:

```sh
node scripts/zkir/bootstrap-native.mjs /private/tmp/nightlean-native-zkir
```

The helper clones the independent upstream source, checks its exact revision and tracked-file cleanliness, builds with the lockfile, checks the CLI version, and writes `bin/zkir` plus `build-manifest.json` under the supplied directory. Set `NIGHTLEAN_ZKIR_SOURCE` to reuse an existing clean checkout at the pinned revision. `NIGHTLEAN_CARGO` chooses the Cargo executable.

The verified session installed Rust into isolated temporary directories without changing the user's PATH or global Rust setup. The official Apple ARM64 rustup installer had SHA-256 `63752a1919a3a4793173ec70f8f212621a7ce38ba6a246095984482f4de20f9f`, matching the [official installer checksum](https://static.rust-lang.org/rustup/dist/aarch64-apple-darwin/rustup-init.sha256). With that isolated installation, the tested bootstrap command was:

```sh
RUSTUP_HOME=/private/tmp/nightlean-rustup \
CARGO_HOME=/private/tmp/nightlean-cargo \
NIGHTLEAN_CARGO=/private/tmp/nightlean-cargo/bin/cargo \
NIGHTLEAN_ZKIR_SOURCE=/private/tmp/nightlean-backend-spike/midnight-zkir \
node scripts/zkir/bootstrap-native.mjs /private/tmp/nightlean-native-zkir
```

This source checkout belongs to the independent upstream ZKIR repository. The script does not invoke another source-language compiler. Its build command is:

```sh
cargo +1.100.0 build --release --locked --package midnight-zkir --features binary
```

## Key-generation result

The independently built CLI compiled the private-claim entrypoint with `k=9` and `rows=297`:

```sh
MIDNIGHT_PP=/private/tmp/nightlean-proof-params \
/private/tmp/nightlean-native-zkir/bin/zkir compile \
  /private/tmp/nightlean-native-contract/zkir/claim.zkir \
  /private/tmp/nightlean-independent-keys/claim.prover \
  /private/tmp/nightlean-independent-keys/claim.verifier
```

| Output | SHA-256 |
| --- | --- |
| `claim.prover` | `b9b7e5dd38f01468aecf6b698a74905800227a41e3ca7d7ef302dc287fc64e55` |
| `claim.verifier` | `bc1e417d74922fee9a97778a0a00e7f9910e38f356cba94aa2dee0788b3fa536` |

Both files matched the prior native claim keys byte for byte. Ledger acceptance and state-transition evidence belong to the separate native runtime and localnet reports.

## Distribution and dependency audit

The [independent ZKIR 3.2 release](https://github.com/midnightntwrk/midnight-zkir/releases/tag/zkir-3.2.0) publishes a WASM package and checksums, with no native macOS CLI asset. The downloaded `midnight-zkir-v3-3.2.0.tgz` matched release SHA-256 `06b6b9e00939da4df11f54b7eda0ace3ada4adcff5780ad303db483e2096667b`. Its API exposes JSON-to-binary conversion, circuit checks, and proving. It does not expose key generation, which is why this path builds the independent native CLI.

An audit of executable scripts and the `scripts/zkir` and `scripts/preview` package lockfiles found no imports or package dependencies on a source-language compiler or contract adapter. The localnet's native transaction commands invoke `/midnight-node-toolkit` for ledger funding, inspection, submission, and state reads. The running localnet relay uses pinned official Node.js image `node@sha256:e67514e5d0f6c46656005e1b693b2ec9d52e80b641307de684d4a015ba7a4eaf`, using only Node's TCP API.

After the final source-derived native claim passed at blocks 398 and 401, `node scripts/localnet/stack.mjs restart-relay` replaced only Nightlean's owned relay. The node, proof server, and indexer retained their containers and state. Finalized height remained 425 before and after replacement, with finalized hash `0x4fe75d3368a4174ef89292e859624b1f305a9a831de287e000451cb05743281f` and the same development genesis. Node RPC, proof-server health, and indexer GraphQL all passed through the replacement relay. Loopback ports 19944, 16300, and 18088 stayed the same. No running Nightlean service uses the earlier JavaScript toolkit image.

Historical research and adapter experiments describe earlier evidence. They do not define this independent toolchain's build or runtime dependencies.
