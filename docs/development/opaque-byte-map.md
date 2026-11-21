# Opaque Map values

Use `OpaqueBytes` for variable-length byte payloads stored as public Map values.
The selected route uses `Bytes32` keys and an opaque byte leaf. The native host
accepts `{"kind":"opaqueBytes","values":[0,1,255]}` as a payload and returns the
original bytes on read. Public ledger state retains the raw bytes. The circuit
uses one field projection and the same raw value supplies the state write.
[Lean fixture](../../tests/OpaqueByteMap.lean)

FAB stores one `Compress` atom. An empty payload projects to zero. A nonempty
payload projects to the pinned length-bound transient commitment. The native
codec rejects nonempty payloads ending in zero and caps payloads at 1 MiB.
[Pinned Compact reference](../../tests/compact/opaque-bytes.mjs)

Use `OpaqueString` as a public value in a root `Bytes32` Map. The native host
accepts and returns `{"kind":"opaqueString","value":"é\u0000λ"}`. Storage
preserves the exact UTF-8 bytes, including an embedded NUL, and binds the same
single `Compress` field in the circuit. Empty strings are valid. The codec
rejects a trailing NUL, malformed UTF-8 in stored state, and opaque byte
payloads presented to a string entrypoint. The string limit is 1 MiB of UTF-8.
[Lean fixture](../../tests/OpaqueStringMap.lean) · [Native check](../../runtime/tests/opaque_string_map.rs) · [Compact reference](../../tests/compact/opaque-string-cases.mjs)

```sh
lake exe noctium compile tests/OpaqueByteMap.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/opaque-byte-map
NOCTIUM_OPAQUE_MAP_DIR="$PWD/build/opaque-byte-map" \
  cargo test --locked --manifest-path runtime/Cargo.toml --no-default-features \
  --features zkir-321 --test opaque_byte_map \
  opaque_bytes_map_round_trips_and_binds_one_compress_field -- --ignored --exact
```

The check uses the freshly emitted plans and relations. Full opaque type
equivalence, other containers and an isolated ledger transaction remain open.
[Native check](../../runtime/tests/opaque_byte_map.rs)
