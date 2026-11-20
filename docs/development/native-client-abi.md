# Native client C ABI

The native C ABI lets a C or C++ host drive Noctium's Rust proof and transaction client. The ABI uses explicit request and reply calls. Rust owns asynchronous work and its typed request mailboxes, then delegates to the same `BoundTransaction` and `SubmissionAttempt` state machine used by the Rust SDK. No foreign callback, borrowed buffer, or foreign stack frame survives a call.

Phase A proves and verifies a retained statement, then keeps the typed `ProvedIntent` inside a proof session. Phase B takes that exact deployment or call intent through funding, signing approval, submission, finalized receipt validation, and durable private journal recovery. Phase A's numeric `requestId` stays unchanged. Phase B's `u64` request identities and `u128` budgets use canonical decimal JSON strings. The ABI rejects stale, crossed, duplicate, malformed, and wrong-token replies before state changes.

The generic client ABI chooses no endpoint, wallet, entropy source, filesystem, or signing policy. Hosts provide chain, funding, signing, and journal capabilities. Phase B accepts checked typed replies from its Rust host adapter. It does not accept caller-asserted receipt JSON. Recovery loads the current full record and storage revision through the journal capability, then reobserves finalized chain state before any private compare-and-swap. An unknown broadcast remains uncertain and keeps the exact sealed transaction for reconciliation. Cancellation after submission rejects. Detach waits for durable acknowledgement. Retrying a failed cancellation or deadline persistence only retries persistence.

The optional `localnet` feature supplies one explicit development adapter. It restricts calls to the qualified loopback endpoint and isolated development genesis. It uses existing Rust node, funding, sealing, and directory-journal code. This adapter does not select a production wallet or endpoint. No Node or Compact process runs in the C++ application's proof or transaction path. Node was used only by a separate development observer to inspect finalized receipts and full state.

## Build and use

Build the shared library with Rust 1.100.0 and the selected proof profile. Profile 3.2.0 is the default. For 3.2.1, select `zkir-321` explicitly.

```sh
cargo +1.100.0 build --manifest-path runtime/Cargo.toml --locked --lib --features localnet
cargo +1.100.0 build --manifest-path runtime/Cargo.toml --locked --lib --no-default-features --features zkir-321,localnet
```

Include [`noctium_native.h`](../../runtime/include/noctium_native.h), link `libnoctium_runtime`, and call the `noctium_client_*` functions for phase B. The header documents descriptor fields, request correlation, token ownership, limits, and localnet helper configuration. [`native_client_cpp_smoke.cpp`](../../runtime/tests/native_client_cpp_smoke.cpp) is the linked qualification host. Its `run` mode writes a private recovery reference for a second process; keep that file private. Its `recover` mode needs the public descriptor, localnet configuration, and that private reference. The complete two-process run also needs the retained public bundle, private proof configuration, trusted SRS, and funded isolated localnet. The evidence file records the qualified inputs by digest without publishing private configuration or journal contents.

Compile the checked-in host against the library built for the same profile:

```sh
clang++ -std=c++17 -Wall -Wextra -Werror runtime/tests/native_client_cpp_smoke.cpp \
  -L"$LIBDIR" -lnoctium_runtime -Wl,-rpath,"$LIBDIR" \
  -o /tmp/noctium-native-client-cpp

/tmp/noctium-native-client-cpp run PROOF_DESCRIPTOR PRIVATE_CONFIG TRUSTED_SRS \
  CLIENT_DESCRIPTOR LOCALNET_CONFIG RUN_RECORD PRIVATE_RECOVERY_REFERENCE
/tmp/noctium-native-client-cpp recover CLIENT_DESCRIPTOR LOCALNET_RECOVERY_CONFIG \
  PRIVATE_RECOVERY_REFERENCE RECOVERY_RECORD
```

The run and recovery records contain sealed transaction bytes and full state. Keep them with the private recovery reference. The published evidence contains receipt identifiers and digests only.

The localnet fixture stages a host-owned Boolean `claims/accepted` value to exercise the private journal protocol. It does not establish general execution or proof of source-declared private effects through this ABI. The source claim and Rust client cover separate paths.

## Qualification

The published implementation is commit `7346401d8521ed32e36727ed42c6659d55dd2923`, tree `5b6be85f2adff7286b83c018f71afa8bcea9e377`. Frozen qualification source hashes bind the eight changed runtime files. The independently qualified snapshot matches all 81 tracked runtime files and their Git modes in the published commit.

Both 3.2.0 and 3.2.1 passed the worker's ordinary Rust suite and six retained-material proof/ABI tests. The linked C++ client deployed the retained contract, made the claim, lost a submission acknowledgement, restarted in a separate process without witness, seed, funding, or signing inputs, and recovered by resubmitting identical sealed bytes. An independent C++ rebuild repeated both profile runs. A stale private writer was rejected before broadcast. The accepted claim committed private state once. A separate development observer matched all eight finalized receipts and full contract-state byte strings against the loopback node. The published source also passed [CI](https://github.com/awjreynolds/noctium/actions/runs/43998040599).

Counts, source hashes, native binary identities, public receipt IDs, full-state digests, and independent qualification records are in [native client ABI evidence](../../tests/native-client-abi-evidence.json). This is an isolated development-network qualification. It does not prove consensus finality, universal compiler correctness, source-effect execution, business-spec correctness, or public-network behavior. The node, proof parameters and keys, entropy, external service policy, signing approval, and durable journal store remain host trust assumptions. Cancellation does not hard-stop in-flight CPU or transport work. The ABI makes no blanket native-memory erasure claim. TypeScript/WASM, Kotlin, and Swift bindings remain future goals.

## Read Merkle snapshots

`noctium_ledger_collection_page` reads ordinary and historic Merkle trees
from exact tagged `ContractState` bytes. Supply the plan and snapshot hashes
from trusted artifacts for the same contract. The reader checks the complete
byte strings, the target profile and the selected path. For a nested tree,
supply the typed public map keys in traversal order.

Page queries use `offset` and `limit`. Every Merkle page includes a decimal
`root` and `firstFree`. Historic pages return their stored roots in `entries`
and a `nextOffset` for subsequent pages. Keep the same snapshot and plan for
every page. An ordinary tree has no history entries.

Use `merklePath` in place of both pagination fields. Omit the index for a
stored-leaf search, or supply a canonical decimal UInt64 index for a
candidate path. Indexed queries return sibling fields and directions in
leaf-to-root order, plus the snapshot and candidate roots. A candidate path
reconstructs the snapshot root when those roots match. Use a search to
require a stored match. An unsuccessful search has null candidate root and
steps. Sparse branches and indices beyond capacity reject.

Field, structured, typed curve, prehashed and raw FAB leaves all use the
pinned ledger leaf hash. Foreign curve inputs require ZKIR 3.2.1. The FAB
form accepts checked nonopaque atoms and bounds the expanded representation
to 1 MiB. See the request and result fields in the
[C header](../../runtime/include/noctium_native.h).

The read path uses only the plan header and state declarations. The test
constructs tagged ledger snapshots with the pinned Rust ledger API, then
compares Rust and C++ reads to Compact. Emitting Merkle operations from Lean
and submitting a transaction are separate compiler and runtime work.

```sh
profile=zkir-321
cargo +1.100.0 build --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features "$profile" --lib
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/merkle-reads.XXXXXX")
trap 'rm -r -- "$scratch"' EXIT
libdir="$(cd runtime/target/debug && pwd)"
c++ -std=c++17 -Wall -Wextra -Werror -I runtime/include \
  runtime/tests/collection_cpp_smoke.cpp -L "$libdir" -lnoctium_runtime \
  -Wl,-rpath,"$libdir" -o "$scratch/merkle-cpp"
NOCTIUM_COLLECTION_CPP="$scratch/merkle-cpp" \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
    --no-default-features --features "$profile" --test merkle_reads
```
