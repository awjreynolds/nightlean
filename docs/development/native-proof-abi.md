# Native proof ABI phase A

Noctium's phase A native proof ABI lets a host authenticate a native bundle, prepare one proof session, obtain a proof request, and ask the Rust runtime to verify and attach a returned proof. The C ABI is declared in [`noctium_native.h`](../../runtime/include/noctium_native.h). [`native_cpp_smoke.cpp`](../../runtime/tests/native_cpp_smoke.cpp) shows a linked C++ caller and its adversarial reply checks. The exported `NOCTIUM_*` names remain Noctium compatibility identifiers.

Phase A ends with an unfunded, unsubmitted public intent projection. Its bounded completed session retains the typed, unsealed `ProvedIntent` internally until the host frees the session. Phase A exposes no private-intent serialization or funding operation. The [phase B native client ABI](native-client-abi.md) extends the header with explicit funding, signing, submission, receipt, and journal requests while preserving phase A behavior.

## Build and qualify

Run commands from the repository root with the qualified Rust 1.100.0 toolchain. The default feature selects profile 3.2.0. Select 3.2.1 explicitly with `--no-default-features --features zkir-321`.

```sh
cargo +1.100.0 build --manifest-path runtime/Cargo.toml --locked --lib
cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked --test native_ffi --test native_proof -- --include-ignored
```

For profile 3.2.1, add `--no-default-features --features zkir-321` after `runtime/Cargo.toml` in both commands. Qualification requires host-provided test bundle and trusted manifest digest, private configuration, SRS bytes and trusted SRS digest, and the optional alternate verifier fixture. Set `NOCTIUM_TEST_BUNDLE`, `NOCTIUM_TEST_MANIFEST_SHA256`, `NOCTIUM_TEST_PRIVATE_CONFIG`, `NOCTIUM_TEST_PROOF_PARAMETERS` and `NOCTIUM_TEST_PROOF_PARAMETERS_SHA256` in the test host environment. The descriptor profile is `midnight-ledger-9` for 3.2.0 or `midnight-ledger-9-zkir-3.2.1` for 3.2.1. The checked-in C++ fixture accepts a public descriptor path, private configuration path, and SRS path as its three arguments; it links against `libnoctium_runtime` and uses host `getentropy` for fresh 32-byte entropy.

Link the fixture against the directory containing the library built by Cargo, then pass the three input paths:

```sh
c++ -std=c++17 -Wall -Wextra -Werror runtime/tests/native_cpp_smoke.cpp \
  -L"$LIBDIR" -lnoctium_runtime -Wl,-rpath,"$LIBDIR" -o /tmp/native-proof-cpp
/tmp/native-proof-cpp /path/to/public-descriptor.json /path/to/private-config.json /path/to/srs
```

The published phase A qualification and bounded evidence are recorded in [native proof ABI evidence](../../tests/native-proof-abi-evidence.json). The worker suite and independent qualification are reported separately. Independent qualification passed six real Rust proof/ABI cases per profile, one live-work accounting case, one early artifact-budget case, and a linked C++ positive/adversarial proof run per profile. The worker's ordinary suite reported 109 passes for 3.2.0 and 110 for 3.2.1, with no failures. Those totals are separate from the real-proof cases.

## Host call sequence

1. Build a UTF-8 JSON descriptor with ABI version 1, the selected profile name, the explicitly authorized bundle directory, independently trusted lowercase manifest and SRS SHA-256 digests, degree `k`, TTL, service capability, and a response limit no larger than 1 MiB. Pass descriptor bytes, private configuration bytes, SRS bytes, and 32 fresh unpredictable entropy bytes through separate arguments to `noctium_native_begin`. Bundle and SRS validation precede private configuration parsing. The host supplies the trust decisions and entropy quality.
2. Call `noctium_native_advance` to receive ordinary result metadata for a `need_proof` request. Its correlation fields include `requestId`, operation, capability, profile, encoding, and bounds. Repeated calls return the same pending request. Treat `requestId` as an exact unsigned 64-bit integer: phase A values exceed JavaScript's safe integer range, so JSON consumers must preserve integer precision.
3. Call `noctium_native_private_request` to obtain a private token. Read it only through `noctium_native_private_length` and `noctium_native_private_copy`, then release it with `noctium_native_private_free`. This separate owned-buffer channel contains the witness-bearing official proof-service payload. Ordinary result access rejects private tokens. The host decides whether a service receives this payload and applies endpoint, privacy, response-allocation, and deadline policy.
4. For local proving, pass the private token and a second fresh 32-byte entropy value to `noctium_native_local_prove`. For an external service, send the private payload under host policy and obtain its raw versioned V2 proof response. Both routes produce a proof response token or bytes for `noctium_native_resume`.
5. Resume with JSON correlation metadata and the raw V2 response. Rust checks the exact frozen statement and proof against retained verifier material and SRS, attaches the typed ledger proof, rechecks binding, and roundtrips serialization before returning the result. Wrong, stale, or crossed metadata and adversarial proof replies fail while the pending request remains available.
6. Read the ordinary result token through `noctium_native_result_length` and `noctium_native_result_copy`, then release it with `noctium_native_result_free`. It contains `publicIntentHex`, its SHA-256, and `funded:false` and `submitted:false`. The projection replaces private Pedersen randomness with its public commitment. The private typed `ProvedIntent` stays inside the bounded session until `noctium_native_free`.

Free result and private tokens after use. Caller-owned copies remain the host's responsibility after token release. Revocation/free zeroizes owned private payload buffers on a best-effort basis. No blanket native-allocation wiping guarantee exists. Cancellation revokes pending tokens and discards late results, but does not stop already-running CPU work. In-flight work retains its resource slot until return. Hard CPU stops require a host worker with a termination policy.

The ABI allows at most 8 sessions, 2 live prepare/prove/verification calls, 64 ordinary result tokens, and 16 private tokens. Private configuration, requests, proof responses, and results are capped at 1 MiB; descriptor and reply metadata at 64 KiB; declared bundle payload at 16 MiB; and SRS bytes at 128 MiB. These are host/resource limits for this ABI, not compiler capability limits.

This API's checks establish the retained verifier key's relation for the exact native statement. They do not prove a general connection from Lean source through compiler output to generated keys, nor audit the full native source or compiler. Bundle digests authenticate bytes only. The host remains responsible for source-certificate authority, native implementation/key generation, SRS ceremony relations, service authorization, and entropy quality. Phase B's implementation and qualification are recorded in [native client ABI evidence](../../tests/native-client-abi-evidence.json). TypeScript/WASM, Kotlin, and Swift SDKs remain goals.
