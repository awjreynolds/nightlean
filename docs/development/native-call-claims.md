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

## Checked two-call partition

The Rust assembly helper checks a caller and leaf callee against their native
circuits, replays both programs from the supplied initial contexts, installs
nonzero communication randomness and checks the resulting preimages. It requires
fresh initial claim sets, one caller claim with sequence zero, the exact callee address, entrypoint hash and
commitment, and no callee claims. Commitments must be distinct. It then uses the
official transcript partitioner. The initial contexts are supplied by the
application. This check does not authenticate them against a network.

The focused source/native case consumes `NativeCallClaims.claim` and the existing
`NativeReturns.advance` artifacts. It checks active and inactive claims, typed
input/output commitment matching, exact effects, rejected target mismatch and rejection of a preloaded claim masquerading as an inactive call.
Source guards reject private addresses, hashes, commitments and control without
release.

This is a checked native partition, not a finalized two-contract deployment.
Intent assembly with retained verifier keys, proof generation and local ledger
acceptance remain open. General call graphs, wider argument types and helper or
hosted-witness statement authoring need further implementation. The reference
state interpreter rejects active call claims rather than simulating a remote call.
