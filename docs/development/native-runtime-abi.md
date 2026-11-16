# Native runtime ABI v1, first provider slice

The Rust runtime now exports an in-process C ABI. A linked C++ host supplies the accepted private claim's five private inputs, obtains the expected public nullifier, and runs the official native circuit checker. Neither execution nor the linked harness invokes Node. The compiler remains written in Lean.

This is the first slice of issue 31. General source witness functions, application provider capabilities, private-state journals and commit/retry semantics remain outstanding. Kotlin, Swift, WASM and TypeScript bindings have not been built or qualified. This ABI produces a checked execution summary. It does not generate a cryptographic proof or submit a transaction.

## Version and representation

The header is `runtime/include/nightlean_runtime.h`. Cargo builds `rlib`, `cdylib` and `staticlib` artifacts. ABI version 1 uses explicit UTF-8 JSON buffers, without a trailing NUL. No Rust layout crosses the boundary. Binary encodings require a separate versioned contract.

The supported profile is `midnight-ledger-9-zkir-3.2.0`. The exact Rust source revisions remain those recorded in [native-rust-runtime.md](native-rust-runtime.md). This work does not upgrade to ZKIR 3.2.1. The npm distribution and native ledger crate versions differ. Existing canonical state/transcript vectors qualify their shared behavior.

Native field values are canonical decimal strings, with no sign, whitespace or redundant leading zero. Values must be smaller than the BLS12-381 scalar modulus. Bool values are JSON booleans. JavaScript numbers and string booleans reject. Only explicitly public output declarations enter completion results.

The unsigned scalar extension uses normalized `UIntRange<N>` types and canonical decimal strings in `[0,N)`, with exclusive bound at most `2^248`. Its checked arithmetic, conversion and provider rules are recorded in [native-unsigned-scalars.md](native-unsigned-scalars.md).

## Host protocol

`nightlean_session_begin` consumes this envelope:

```json
{
  "abiVersion": 1,
  "profile": "midnight-ledger-9-zkir-3.2.0",
  "plan": { "schemaVersion": 1 },
  "publicInputs": {},
  "state": {},
  "ledgerParametersHex": "...",
  "address": "...",
  "circuit": {}
}
```

`plan`, `state`, serialized ledger parameters and circuit use the existing qualified artifact formats. The abbreviated objects above show envelope fields, not a runnable fixture. `publicInputs` must contain exactly every declared public input. Private inputs reject in this object. The address is exactly 32 bytes encoded in hex. Unknown envelope fields reject. The artifact producer and target profile remain trusted for circuit/plan correspondence. This slice does not verify a signed or content-addressed artifact manifest.

Begin returns a session token and a `ready` result token. The host calls `nightlean_session_advance`. Each missing private input yields a request in declaration order:

```json
{"abiVersion":1,"status":"need_host","request":{"id":1,"operation":"witness.input","name":"secret","type":"Native","visibility":"private"}}
```

The host performs storage access, networking, prompting or other asynchronous work outside the library, then calls `nightlean_session_resume` with:

```json
{"abiVersion":1,"requestId":1,"value":"42"}
```

A matching, well-typed response produces `ready`. Wrong IDs, duplicate responses, unsolicited responses, unknown response fields and noncanonical values reject. A rejected response preserves the pending request. Repeated advance returns the same pending request. Only one request exists per session, with no nested host callback stack.

After all private inputs arrive, advance evaluates the plan, executes native Impact operations, partitions transcripts with the supplied ledger cost model, constructs the diagnostic preimage and runs the official ZKIR checker. Completion returns only declared public outputs and operation counts:

```json
{"abiVersion":1,"status":"completed","result":{"publicOutputs":{},"operations":21,"activityGroups":21,"officialCircuitChecked":true,"proofGenerated":false,"transactionSubmitted":false,"privateStateJournal":null}}
```

Circuit rejection produces `failed` with the fixed error code `execution_rejected`. Neither failure results nor numeric API errors echo private input values. Completion is repeatable until release. Cancellation yields `cancelled`, clears retained input strings and prevents resumption. Terminal completed/failed sessions reject cancellation. Releasing an incomplete session also discards retained inputs.

## Ownership, limits and failures

Sessions and results use process-local integer tokens in separate registry maps. Zero, stale and unallocated tokens reject without dereferencing foreign session pointers. Tokens are monotonic and never reused. They are not security capabilities against another caller inside the same process.

Input memory belongs to the caller and is borrowed only for each call. Results belong to Rust and remain valid until `nightlean_result_free`. Query the byte length, provide a caller-owned buffer, then copy. A short buffer returns `NIGHTLEAN_BUFFER_TOO_SMALL`, writes zero bytes and performs no partial copy. The result has no NUL terminator. Session release does not release result tokens. Every successful allocation needs its corresponding free.

Non-null pointers still require readable or writable memory of the declared size and correct alignment. Input buffers and output storage must not overlap. Output storage regions must not overlap one another. Rust cannot validate arbitrary native addresses. Invalid pointers, allocator exhaustion and aborts lie outside panic recovery. Every fallible exported function catches unwinding Rust panics and returns `NIGHTLEAN_INTERNAL`. The library does not replace the application's global panic hook. Applications should avoid panic hooks which log sensitive application context.

The current implementation limits each input or result JSON buffer to 1 MiB, live sessions to 64, live results to 256, plan/circuit instruction counts to 4096, declared inputs/outputs/reads to 256 and native state slots to 16. Native field parsing bounds decimal length before big-integer allocation. These are bounded interface limits, not a hostile-code memory or CPU sandbox. Qualified artifacts remain the intended input. The supported operation whitelist excludes arbitrary ZKIR execution such as general exponentiation.

Calls serialize through one registry mutex. The host must wait for an active call before releasing its session. Cancellation takes effect between calls and does not interrupt a checker already running. No callback, filesystem access, network access, wallet key access or ambient time access occurs in this library. The CLI and fixture preparation script read files separately. Retained JSON strings receive best-effort zeroization on completion, cancellation and release. Temporary parser, field arithmetic and upstream dependency copies have no complete zeroization guarantee.

## Reproduce the linked checks

Build with the pinned Rust toolchain. `QUALIFIED_ARTIFACTS` denotes the accepted native artifact directory, including `source-plan.json`, `runtime-config.json`, `ledger.params`, `native-contract.json` and `zkir/claim.zkir`.

```sh
cd runtime
cargo build --locked
cargo test --locked
cd ..
python3 runtime/tests/prepare_abi_fixture.py "$QUALIFIED_ARTIFACTS" /tmp/nightlean-abi-public.json
```

The preparation script writes only the plan, public inputs, public ledger state, parameters, address and circuit. The test host supplies fixed, synthetic private values from its own test source. It does not put production witness material into the public artifact bundle.

For macOS, set `RUNTIME_LIB` to the Cargo debug artifact directory:

```sh
clang -std=c11 -Wall -Wextra -Werror -I runtime/include runtime/tests/c_smoke.c \
  -L "$RUNTIME_LIB" -lnightlean_runtime -Wl,-rpath,"$RUNTIME_LIB" -o /tmp/nightlean-c-smoke
clang++ -std=c++17 -Wall -Wextra -Werror -I runtime/include runtime/tests/cpp_smoke.cpp \
  -L "$RUNTIME_LIB" -lnightlean_runtime -Wl,-rpath,"$RUNTIME_LIB" -o /tmp/nightlean-cpp-smoke
env -i PATH=/usr/bin:/bin /tmp/nightlean-c-smoke
env -i PATH=/usr/bin:/bin /tmp/nightlean-cpp-smoke /tmp/nightlean-abi-public.json
```

The C harness checks symbol linkage, version, null inputs and invalid tokens. The C++ harness checks real claim execution, the expected public nullifier, a rejected wrong secret, request ordering, repeat advance, wrong IDs, Native/Bool validation, duplicate or unsolicited resume, cancellation, short copy buffers, explicit release and stale-token rejection. The existing native CLI remains the state-byte, five-negative-case and replay qualification check.
