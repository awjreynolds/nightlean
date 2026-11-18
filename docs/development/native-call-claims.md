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
contexts. Resolving deployed verifier keys, attaching verified proofs and
submitting a balanced transaction on localnet remain separate work. Wider
arguments, typed source call declarations and helper or hosted-witness
statement authoring remain open. The reference state interpreter rejects
active call claims.
