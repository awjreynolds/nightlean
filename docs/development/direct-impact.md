# Direct ledger transcript conformance

The Lean native backend compiles the private claim relation and state guards
without Compact. `Nightlean.Backend.Impact.lower` builds a symbolic native VM
plan. `Nightlean.Backend.Zkir.lowerEntrypoint` binds its complete field encoding,
including opcodes, alignments, keys, read results, and write values.

The state layout is a root array in declaration order. Native and boolean cells
use Native field alignment. Native VM map membership produces a byte-aligned
boolean. The lowerer binds each membership result to false before inserting the
nullifier. A circuit assertion binds the read root and campaign to the public
parameters. A state read alone does not enforce either comparison.

## Reproduce

Run from the repository root with the pinned Lean toolchain:

```sh
lake build Nightlean.Backend.Zkir Nightlean.Claim
mkdir -p build/direct-impact
lake env lean --run tests/Impact.lean > build/direct-impact/operations.json
lake env lean --run tests/Impact.lean --zkir > build/direct-impact/claim.zkir
npm ci --prefix scripts/zkir
node scripts/zkir/check-impact.mjs build/direct-impact/operations.json build/direct-impact/claim.zkir
```

The fixture uses public, deterministic test inputs. Its secret is 42, campaign
is 7, siblings are 17 and 23, and directions are false and true. Domain tags
1, 2, and 3 are Nightlean application choices. The Lean operation fixture uses
root 99 and nullifier 123 as placeholders. The harness replaces those values
with the pinned ledger package's native hash results before constructing the
proof preimage and executing the VM.

## Verified boundaries

The locked dependencies are `@midnight-ntwrk/ledger-v9` 1.0.2 and the official
`@midnightntwrk/zkir-v3` 3.2.0 release tarball.

The official ZKIR implementation accepts the generated relation and its ledger
proof preimage. This covers preprocessing and assertion checking, with the
native full-transcript encoding rather than a synthetic list of public values.
The fixture has k=9 and serializes to 2,451 bytes.

Negative preprocessing checks reject a wrong secret, public root, public
campaign, stored root, and stored campaign. The native ledger VM separately
executes the matching transcript, records the nullifier, and rejects replay
because membership returns true where the transcript binds false. The initial
state stays unchanged. The immutable successful state remains intact after the
failed replay.

This harness does not generate a cryptographic proof, verify a proof, submit a
transaction, or establish Preview acceptance. Those stages require native key
generation and transaction integration. The VM and preprocessing checks are
reported separately in the JSON output.

## Encoding references

- [Ledger 9 VM opcode field representation](https://github.com/midnightntwrk/midnight-ledger/blob/ledger-9.1.0.1/onchain-vm/src/ops.rs)
- [Ledger aligned-value field representation](https://github.com/midnightntwrk/midnight-ledger/blob/ledger-9.1.0.1/transient-crypto/src/fab.rs)
- [Proof preimage construction from native operations](https://github.com/midnightntwrk/midnight-ledger/blob/ledger-9.1.0.1/onchain-runtime-wasm/src/primitives.rs)
