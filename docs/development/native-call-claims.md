# Native call-claim references

The direct contract entrypoint path supports Midnight's call-claim operation:

```lean
claimContractCall(target, entryHash, disclose(commitment))
```

`target` and `entryHash` have type Bytes32. `commitment` is a Native field.
The operation records a reference to another call. It does not execute a remote
witness provider or construct a complete transaction. The ledger generates the
claim's sequence number from its current claim set.

Lean emits one checked Impact operation with nine activity groups. Rust expands
the pinned ledger's `kernel_claim_contract_call!` macro. The same guard applies to
all nine VM operations. The operation targets the kernel effects map, not a
contract state field. Address, entrypoint hash, commitment and private control
dependencies require explicit authorized disclosure before reaching this sink.

## Binding input and output

Midnight's communication commitment hashes the opening followed by the flattened
call input and output fields. The scalar example uses the existing Native hash:

```lean
disclose(transientHashNativeVector([
  opening, argument, expectedBalance,
  cast(Native, expectedCount), cast(Native, expectedEnabled)]))
```

These fields match `NativeReturns.advance`: one committed Native argument and
Native balance, UInt64 count and Bool return values. The entrypoint hash comes
from the official `EntryPointBuf.ep_hash()` domain. The commitment does not bind
alignment metadata or a type schema, so callers must also select and validate the
callee's interface. Passing a field reference alone does not establish this
payload binding.

## Assemble a native call forest

The Rust SDK takes prepared calls in ledger execution order through
`assembly::assemble_checked_calls`. Each call has a circuit, an initial
`QueryContext`, an entrypoint and a fresh private communication opening. The
helper replays each program from its supplied context and checks the resulting
state and effects. It uses Midnight's partitioner to split guaranteed and
fallible operations across the forest.

Every recorded claim must match a later call's address, entrypoint hash and
communication commitment. Commitments must be distinct, and each callee has
at most one incoming claim. The ledger's sequencing check enforces sibling
order and transcript causality. The intent carries both transcript sections
and the private proof preimages. The helper checks each reconstructed preimage
and activity schedule against its circuit. Key locations use
`<hex-address>:<entrypoint>` so equally named operations at different
addresses have separate resolver entries.

The focused case assembles `NativeCallClaims.claim`, its claimed
`NativeReturns.advance` callee and an independent call to another address
in one intent. It checks the ordered calls and the committed Native argument.
Missing, reversed and wrong targets, duplicate commitments and preloaded
effects reject. When the claim guard is false, the caller assembles by itself.
Source guards reject private addresses, hashes, commitments and control without
release.

The result is a private, unbalanced intent. Applications supply the initial
contexts. Wider arguments, typed source call declarations and helper or
hosted-witness statement authoring remain open. The reference state interpreter
rejects active call claims.

## Prove a composed intent

`proof::PreparedComposition::from_intent` freezes the assembled intent.
Pass a host-authenticated ledger snapshot and a `CompositionMaterial` for
each call in intent order. Each selection contains its authenticated public
bundle and trusted proof parameters. The SDK compares the bundle's ledger
parameters with the snapshot and its verifier key with the operation installed
at the call's address and entrypoint. These checks precede proof requests.

`prove_locally` uses host-provided entropy. `prove` accepts a host-authorized
proof service. Each proof binds its own call statement and the shared intent
commitment. The SDK verifies every response, attaches the native V3 proofs
and verifies the attached statements again before returning a proved intent.

The focused case generated keys from fresh Lean exports and attached k=9 and
k=8 proofs to one intent. A snapshot with the caller's key installed for the
callee rejected before proving. The sealed transaction passed the pinned
ledger's in-process verification with fee balancing disabled. Funding,
submission and finalized state on a running localnet remain open.

To reproduce, compile [the caller](../../tests/NativeCallClaims.lean) and
[the callee](../../tests/NativeReturns.lean) with the ZKIR 3.2.1 target.
Generate keys with the pinned [native ZKIR tool](native-toolchain.md).
Assemble the two [public bundles](portable-artifacts.md) as `caller-bundle`
and `callee-bundle`, selecting `claim` and `advance` respectively, with
identical ledger parameters. Set `NOCTIUM_COMPOSITION_BUNDLES` to their
absolute parent path. Supply the independently trusted manifest digests as
`NOCTIUM_COMPOSITION_CALLER_SHA256` and `NOCTIUM_COMPOSITION_CALLEE_SHA256`.
Set `NOCTIUM_COMPOSITION_SRS` to the public SRS directory and provide the
k9 and k8 digests as `NOCTIUM_COMPOSITION_CALLER_SRS_SHA256` and
`NOCTIUM_COMPOSITION_CALLEE_SRS_SHA256`.

```sh
cargo test --manifest-path runtime/Cargo.toml --locked \
  --no-default-features --features zkir-321 --test native_composition -- --include-ignored
```
