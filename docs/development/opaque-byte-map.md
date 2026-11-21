# Opaque byte Map values

Use `OpaqueBytes` for variable-length byte payloads stored as public Map values.
The selected route uses `Bytes32` keys and an opaque byte leaf. The native host
accepts `{"kind":"opaqueBytes","values":[0,1,255]}` as a payload and returns the
original bytes on read. Public ledger state retains the raw bytes. The circuit
uses one field projection and the same raw value supplies the state write.
[Lean fixture](../../tests/OpaqueByteMap.lean)

FAB stores one `Compress` atom. An empty payload projects to zero. A nonempty
payload projects to the pinned length-bound transient commitment. The native
codec rejects nonempty payloads ending in zero and caps payloads at 1 MiB.
`OpaqueString` remains a separate sealed constructor metadata type.
[Pinned Compact reference](../../tests/compact/opaque-bytes.mjs)

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
