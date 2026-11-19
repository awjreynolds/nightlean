# Standard public events

Use `emitEvent` inside a ledger entrypoint. The [example](../../examples/StandardEvents.lean) emits `Paused`, optionally follows with `ShieldedSpend`, then emits `Unpaused`.

```lean
emitEvent(Paused)
when active emitEvent(ShieldedSpend, disclose(nullifier))
emitEvent(Unpaused)
```

The current source surface recognizes these three standard layouts. A `ShieldedSpend` payload has exactly 32 bytes. The pause events have empty payloads. Both the payload and the decision to emit are public effects. A private payload or guard requires an explicit `disclose`. Event syntax is limited to entrypoint bodies. Logging a nullifier publishes the value. The example uses a synthetic value and exercises logging itself. [Pinned standard event catalog](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/midnight-events.ss) · [Disclosure policy](disclosure.md)

Lean emits two Impact groups per event, a push of the version, tag and typed data cells, followed by `Log`. The ZKIR statement binds the ordered public groups and their activity. Rust simulates the ordered plan and returns the decoded native versioned logs in `Execution::logs`. Those values describe local simulation. The finalized client receipt records the accepted transaction and contract state. [Ledger event format](https://github.com/midnightntwrk/midnight-improvement-proposals/blob/main/mips/mip-0002-public-contract-log-emission.md)

## Focused qualification

With the selected Ledger 9.1.0.1 and ZKIR 3.2.1 profile, native key generation reported K8 and 238 rows. The Rust checker accepted both guard values and checked version, order and exact payload bytes. Substituting the public tape from a different private input failed. Lean rejected implicit private payload and private guard disclosure. On the isolated funded genesis, the Rust client verified the deploy and call below. The native VM simulation checked the decoded logs. Indexer observation and the remaining eight event layouts are open.

| Localnet action | Block | Transaction ID |
| --- | ---: | --- |
| Deploy | 30681 | `63acc78623f42e8dfff51c0a0d0f7b3f0f03e38770a80288ad2fb9c844b74c7a` |
| Call, guard active | 30684 | `d5ef04ce1c2e8e846eacb95abdfa37d83707170a676963c0d198fbb3e2390dbb` |

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
