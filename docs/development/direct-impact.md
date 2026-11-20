# Direct ledger transcript conformance

The Lean native backend compiles the private claim relation and state guards
without Compact. `Noctium.Backend.Impact.lower` builds a symbolic native VM
plan. `Noctium.Backend.Zkir.lowerEntrypoint` binds its complete field encoding,
including opcodes, alignments, keys, read results, and write values.
The relation emits one Impact group for each native VM operation. The checker
returns one activity entry per group, which transaction proving consumes in
operation order. A single group over the same flattened field values passes
standalone checking but fails this transaction-level requirement.
Native contract entrypoints also enable the communication commitment. The
ledger verifier always places this commitment after the binding input in the
proof's public instance. Standalone relations leave this flag disabled.

The state layout is a root array in declaration order. Native and boolean cells
use Native field alignment. Native VM map membership produces a byte-aligned
boolean. The lowerer binds each membership result to false before inserting the
nullifier. A circuit assertion binds the read root and campaign to the public
parameters. A state read alone does not enforce either comparison.

## Reproduce

Run from the repository root with the pinned Lean toolchain:

```sh
lake build Noctium.Backend.Zkir Noctium.Claim
mkdir -p build/direct-impact
lake env lean --run tests/Impact.lean > build/direct-impact/operations.json
lake env lean --run tests/Impact.lean --zkir > build/direct-impact/claim.zkir
npm ci --prefix scripts/zkir
node scripts/zkir/check-impact.mjs build/direct-impact/operations.json build/direct-impact/claim.zkir
```

The fixture uses public, deterministic test inputs. Its secret is 42, campaign
is 7, siblings are 17 and 23, and directions are false and true. Domain tags
1, 2, and 3 are Noctium application choices. The Lean operation fixture uses
root 99 and nullifier 123 as placeholders. The harness replaces those values
with the pinned ledger package's native hash results before constructing the
proof preimage and executing the VM.

## Verified boundaries

The locked dependencies are `@midnight-ntwrk/ledger-v9` 1.0.2 and the official
`@midnightntwrk/zkir-v3` 3.2.0 release tarball.

The official ZKIR implementation accepts the generated relation and its ledger
proof preimage. This covers preprocessing and assertion checking, with the
native full-transcript encoding rather than a synthetic list of public values.
The fixture has k=9 and serializes to 2,610 bytes. Its 21 native VM operations
produce 21 checker activity entries. The harness asserts this count as a
transaction-binding regression check.

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

## Write an ordinary Merkle tree

Declare a root tree with `merkleTree claims : 2`. Use
`insertHash claims := disclose(leafHash)` to append a private Bytes32 digest.
`isFull claims as full` reads the current capacity flag, including after an
append in the same call. `reset claims` restores the default empty tree.
Depths range from 2 through 32. The native runtime rejects appends at capacity.
The compiler rejects a private leaf written without disclosure.

The [Lean fixture](../../tests/MerkleTree.lean) and the
[Compact oracle](../../tests/compact/ordinary-merkle.mjs) use the same
depth-two tree. The native test checks the four append roots and cursors,
the fifth append rejection, a changed capacity result, and exact reset.

```sh
lake build noctium Noctium:shared
mkdir -p build/experiments
scratch=$(mktemp -d "$PWD/build/experiments/ordinary-merkle.XXXXXX")
trap 'rm -rf -- "$scratch"' EXIT
.lake/build/bin/noctium compile tests/MerkleTree.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --output "$scratch/contract"
NOCTIUM_NATIVE_TEST_ARTIFACTS="$scratch/contract" \
  cargo +1.100.0 test --manifest-path runtime/Cargo.toml --locked \
    --no-default-features --features zkir-321 --test ordinary_merkle -- --ignored
```

On the isolated Ledger 9.1.0.1 localnet, the native client finalized deployment
at height 4 and the first append at height 7. The receipt state bytes matched
the native runtime prediction at both steps. The pinned ZKIR 3.2.1 tool
reported k=8 and 231 rows for the append relation.
[Localnet receipt](ordinary-merkle-localnet-receipt.json)
