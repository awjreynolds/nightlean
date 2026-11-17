# OpenZeppelin contract POC

The [implementation milestone](https://github.com/awjreynolds/noctium/issues/68)
rebuilds OpenZeppelin's confidential token with public supply in Lean. The
reference revision is `f85f1a23685c6bbedfc8c2589ae3aa128aff7c46` of
`OpenZeppelin/compact-contracts`. Its composed integration contract supplies the
behavioral benchmark. Its supply operations are deliberately ungated for tests.

Noctium compiles Lean directly to native ZKIR and ledger artifacts. The comparison
uses results, public state, decrypted balance results and native acceptance.
Different instruction sequences and constraint counts are acceptable.

## Implementation order

| Needed capability | Immediate use | Current boundary |
| --- | --- | --- |
| Dynamic map-value and membership reads | Balances, registered keys and allowances | Scalar value reads use native two-part index paths. Membership binds a Bool from the native VM, including after writes. Focused 3.2.1 cases pass and reject forged reads. Missing value keys fail; membership returns false. |
| Multi-entrypoint calls on current state | Registration, transfer and supply calls on one deployed contract | Bundle collection, retained deployment and source/proof/client handoff are implemented. Scalar-only operations also prepare calls without a witness-control sidecar. A focused add/subtract test covers distinct k9/k8 parameters and client startup after one real proof. Integrated multi-operation ledger execution remains open in issue 67. |
| Ledger-backed getter returns | totalSupply, balanceOf and isRegistered | Entrypoint returns are currently empty. Typed outputs checked after ledger effects and actual native CALL return binding remain in [issue 50](https://github.com/awjreynolds/noctium/issues/50). Public transcript reads supply state evidence, not returned function values. |
| Guarded native execution | Missing accounts, balance checks and conditional updates | Scalar reads/writes/require and nested effect-block branches support guarded activity and safe inactive values. Selected-3.2.1 native checks pass; separate write fixtures have real proof/attachment evidence with native Noop/gas agreement. General helper/witness branches and aggregate reads remain open in issue 43. |
| Composite ledger values and byte keys | Account identifiers, encrypted balances and escrow records | Bytes32 keys, nested scalar maps and Native-field record cells have focused 3.2.1 native evidence. Records reuse checked composite schemas and one aligned cell, with guarded reads and per-field disclosure. The four-field fixture qualifies ciphertext-shaped storage. Mixed records, lists and the full Counter ADT remain in [issue 69](https://github.com/awjreynolds/noctium/issues/69). |
| Jubjub and cryptographic source operations | ElGamal balances, key registration and account identifiers | Typed bytes, persistent hashes and curve source operations are tracked in [issue 70](https://github.com/awjreynolds/noctium/issues/70). |
| Lean port integration | Register, mint, transfer, approve, transferFrom and burn | Build after the required feature paths work. |

The complete 47-instruction, 15-type native inventory remains the wider target.
The token workload does not exercise every native instruction.

The first source component is
[`examples/openzeppelin/PublicSupply.lean`](../../examples/openzeppelin/PublicSupply.lean).
It rebuilds the public-supply extension's two accounting blocks with 128-bit
overflow/underflow rejection and explicit public disclosure. It is an ungated
component that still needs atomic pairing with encrypted token effects.
One focused selected-3.2.1 native test checks supply `0 → 5 → 3`, unchanged
initial state, overflow rejection and underflow rejection. It generates no keys,
proof or deployment.

## Reference behavior to retain

The pinned reference exports 16 entrypoints. Its source requires the following
paths, beyond the current scalar map example:

| Entrypoints | Required behavior and implementation owner |
| --- | --- |
| `totalSupply`, `mint`, `burn`, `burnFrom` | Pair supply changes with encrypted token changes atomically. Retain 128-bit supply arithmetic and public mint/burn deltas. [Native state and crypto](https://github.com/awjreynolds/noctium/issues/70). |
| `balanceOf`, `pendingOf`, `allowance`, `isRegistered` | Membership and guarded lookup. Missing entries return valid curve-identity encrypted zeros. Escrow uses nested owner/spender maps and a record containing two ciphertexts and an owner memo. [Ledger ADTs](https://github.com/awjreynolds/noctium/issues/69), [guards](https://github.com/awjreynolds/noctium/issues/43). |
| `computeAccountId`, `registerWithKey` | Exact persistent-hash account identity, domain-separated encryption key ownership, registration uniqueness and encrypted-zero initialization. [Typed crypto](https://github.com/awjreynolds/noctium/issues/70). |
| `transfer`, `_move`, `sweep` | Separate spendable and pending balances. Credit the pending pool, deliver a memo, preserve credit epochs, and sweep through the authenticated encryption key. [Ledger ADTs](https://github.com/awjreynolds/noctium/issues/69), [crypto](https://github.com/awjreynolds/noctium/issues/70). |
| `approve`, `transferFrom`, `burnFrom` | Refund prior escrow, preserve encrypted allowance and owner-readable remaining balance, and bind spend randomness to owner, spender and epoch. [Ledger ADTs](https://github.com/awjreynolds/noctium/issues/69), [crypto](https://github.com/awjreynolds/noctium/issues/70). |
| `clearMemos` | Authenticate the encryption key, check the expected memo epoch and reset the memo list without resetting lifetime credit counters. [Ledger ADTs](https://github.com/awjreynolds/noctium/issues/69). |
| Caller-returning operations | Return the authenticated caller identity, which composing policies use for caller checks. Typed native inputs/returns remain part of [composition](https://github.com/awjreynolds/noctium/issues/50). |

The constructor also retains sealed name, symbol and decimals plus initialization
state. The witness interfaces supply an account secret, an encryption secret,
a plaintext claim indexed by ciphertext, and a fresh invocation randomness seed.
The circuit checks key ownership and plaintext claims. Seed freshness is a wallet
responsibility. Deterministic fixture seeds do not establish production privacy.

These requirements come from the pinned
[token](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/token/ConfidentialFungibleToken.compact),
[composed harness](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/test/integration/_mocks/ComposedConfidentialFungibleTokenPublicSupply.compact),
and [ElGamal helpers](https://github.com/OpenZeppelin/compact-contracts/blob/f85f1a23685c6bbedfc8c2589ae3aa128aff7c46/contracts/src/crypto/ElGamal.compact).
They describe port requirements, not implemented capabilities.

## Minimum checks

Compile each changed feature group. Run one focused native example and one
targeted rejection case where its semantics need one. Reuse existing evidence.
Run one integrated localnet demonstration at the completed-port milestone.
Additional proofs, repeated export audits, broad regression campaigns and
duplicate deployments stay in the assurance backlog.

Historical formal qualification remains attached to its recorded source commit.
New POC features do not inherit those proof claims automatically.
This also applies to conditional writes, membership reads and their SDK proof
integration. Their native checks and proof tests are separate evidence.
The map-read extension needs corresponding changes in `GenericStateOps.lean`,
`GenericStateEffectStep.lean` and `GenericStateConverseEffectStep.lean` before
the generic-state proof suite covers the extended compiler. That work belongs
to the [assurance backlog](https://github.com/awjreynolds/noctium/issues/21).
