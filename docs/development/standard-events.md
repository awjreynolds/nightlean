# Standard public events

Use `emitEvent` with named fields inside a ledger entrypoint. The [example](../../examples/StandardEvents.lean) emits all eleven catalog events in one call and exercises a guarded event in a separate entrypoint.

```lean
emitEvent(Paused)
when active emitEvent(ShieldedSpend, nullifier := disclose(nullifier))
emitEvent(Unpaused)
```

Write arguments in any order. The compiler checks field names, duplicates, required fields, and exact types, then encodes them in the catalog order. Payload values and the decision to emit are public. Each private input to either needs an explicit `disclose`. Presence and address flags are public data too. Both slots of an address choice and the value of an absent optional are encoded. Put zero in slots you want left empty. [Pinned standard event catalog](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/midnight-events.ss) · [Disclosure policy](disclosure.md)

| Event | Named fields in wire order |
| --- | --- |
| `ShieldedSpend` | `nullifier` |
| `ShieldedReceive` | `commitment`, `hasCiphertext`, `ciphertext`, `hasContractAddress`, `contractAddress` |
| `ShieldedMint` | `commitment`, `domainSep`, `hasAmount`, `amount` |
| `ShieldedBurn` | `nullifier`, `hasAmount`, `amount` |
| `UnshieldedSpend`, `UnshieldedReceive` | `isUser`, `userKey`, `contractAddress`, `domainSep`, `tokenType`, `amount` |
| `UnshieldedMint` | `domainSep`, `tokenType`, `amount` |
| `UnshieldedBurn` | `isUser`, `userKey`, `contractAddress`, `tokenType`, `amount` |
| `Paused`, `Unpaused` | Empty |
| `Misc` | `name`, `payload` |

Flags have type `Bool`. Amounts are `UInt 128` and use 16 little-endian bytes. `ciphertext` takes `Bytes 512`, `payload` takes `Bytes 256`, and the other byte fields take `Bytes 32`.

Lean emits two Impact groups per event. The first pushes the version, tag and encoded bytes as three cells. The second executes `Log`. The ZKIR statement binds the ordered public groups and their activity. The Rust runtime returns the decoded native logs in `Execution::logs` during local simulation. [Ledger event format](https://github.com/midnightntwrk/midnight-improvement-proposals/blob/main/mips/mip-0002-public-contract-log-emission.md)

## Focused qualification

On Ledger 9.1.0.1 and ZKIR 3.2.1, native key generation reported K13 and 5,000 rows for the eleven-event call. The pinned Compact 0.36.1 toolchain and its 0.21.0 runtime produced the reference values. Noctium's native checker matched all eleven versions, tags, declared widths and SHA-256 digests of the full-width payloads. The fixtures exercise a 128-bit amount with the high bit set, both address branches, and a wide payload with a trailing zero. Lean rejected an undisclosed private event flag, missing or duplicate fields, and a non-Boolean flag. The separate guarded-event test checks both branches and rejects a substituted public tape.

The first catalog input layout declared the 256-byte memo public. That produced 527 Impact operations, 7,966 rows and a 19,217-byte transaction. The localnet pool returned error 111, `TransactionTooLarge`. The example now selects the memo as a committed argument using nine FAB chunks and explicitly discloses it in the event. This uses 15 Impact operations, produces a 9,918-byte transaction and preserves all eleven payloads. Packing the standard public-byte input path is follow-up optimization work. [Committed call arguments](committed-returns.md#native-call-arguments) · [Node error codes](https://docs.midnight.network/nodes/error-codes) · [Issue 74](https://github.com/awjreynolds/noctium/issues/74)

The funded isolated localnet accepted the catalog deployment and proved call. Indexer delivery and emission from within reusable helper bodies still need qualification.

| Localnet action | Block | Transaction ID |
| --- | ---: | --- |
| Deploy | 30859 | `3ff8bb36d1a37a54b148c26b2b13f813519a756d1cd31bb87a29bdbfc48b1ef2` |
| Call | 30862 | `37b63e6d8d929e8d90d94777ee71e354551db1344fe90f069dfab4388ea87b73` |

```sh
lake build noctium
.lake/build/bin/noctium compile examples/StandardEvents.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output build/experiments/standard-events
NOCTIUM_EVENT_ARTIFACTS="$PWD/build/experiments/standard-events" \
  cargo test --manifest-path runtime/Cargo.toml --locked --no-default-features \
  --features zkir-321 --test standard_events -- --ignored
```

Generate keys, assemble the authenticated bundle and submit with the Rust client for localnet qualification. [Bundle workflow](portable-artifacts.md#build-and-use) · [Native client](native-client.md)
