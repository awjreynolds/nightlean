# Confidential-token integration

`examples/openzeppelin/ConfidentialToken.lean` adapts the registration, credit, sweep, transfer, burn, memo maintenance and query paths from OpenZeppelin's confidential fungible token at
revision `f85f1a23685c6bbedfc8c2589ae3aa128aff7c46`. Noctium compiles the source
directly to native ZKIR and ledger operations. This milestone covers sixteen
entrypoints from the sixteen-entrypoint reference workload.

`registerWithKey` proves the account ID is SHA-256 of the private account secret
and proves ownership of the nonidentity registered encryption key. It initializes
spendable and pending balances with the curve-identity encryption of zero.
`mint` adds encrypted value to pending funds, prepends an ECDH memo, advances the
recipient's credit counter and changes public supply in the same transaction.
`sweep` authenticates the wallet and merges pending funds into spendable funds.
`transfer` proves the sender's plaintext balance, debits spendable funds, and
credits the recipient's pending funds with a memo and counter update.
`burn` authenticates the sender, subtracts encrypted spendable funds and public
supply atomically, and preserves pending funds, memos and credit counters.
`_move` uses the same conserving debit/credit path and permits self-moves.
`transfer` retains its self-transfer rejection. `clearMemos` authenticates both
wallet secrets and checks the current credit epoch before resetting only the
caller's memo List. A stale epoch rejects clearing after a concurrent credit.
The views expose supply, registration, spendable/pending ciphertexts and account
ID computation. Missing ciphertext entries return curve-identity encrypted zero.
Ciphertext results use named typed point components; nominal composite ABI
layouts remain separate work. `approve` refunds the prior owner ciphertext,
proves the refunded spendable balance, then replaces the escrow with paired
owner/spender encryptions and an owner memo. `transferFrom` consumes the
spender-authenticated escrow and credits recipient pending funds. `burnFrom`
consumes escrow and subtracts public supply. Both refresh the owner memo and
advance the permanent owner/spender spend counter. `allowance` returns those encrypted
components, with identity/zero defaults for an absent owner or spender.

| State | Representation |
| --- | --- |
| encryptionKeys | Account ID to two Native key coordinates |
| balances, pending | Account ID to four Native ciphertext coordinates |
| memos | Account ID to a List of three-Native ECDH memo records |
| creditEpochs | Account ID to a native u64 Counter |
| escrow | Owner and spender IDs to two ciphertexts and an owner memo |
| escrowSpendEpochs | Owner and spender IDs to a permanent u64 Counter |
| initialized | Public initialization precondition |
| totalSupply | Public UInt128 supply |

The source takes candidate IDs, points and ciphertext coordinates as circuit
inputs. It checks account IDs against private secrets, keys against registered
keys, and every candidate ciphertext against actual ordered ledger reads before
writing. A candidate input is not trusted state. The account ID is returned as
a typed Bytes32 result bound to the native output commitment.

A witness helper now returns a single logical Bytes32 value directly, with
[focused source/host/native evidence](bytes32-witness-output.md). Approval's
grouped ciphertext result still uses a public account-ID candidate constrained
against the private secret. Records mixing Bytes32 with other output fields
remain separate ABI work. The helper analyzer enforces a maximum expanded depth
of 256. Typed point candidates avoid unused parameters within this bound.

Private account and encryption secrets come from wallet-scoped native witness
reads. A typed callback supplies a UInt248 plaintext claim indexed by the sender's
ciphertext. The circuit checks the claim through ElGamal decryption. The host also
supplies a private seed for encryption and memos. The credit epoch is cast to a
Native/Field before hashing, matching the reference's explicit Field cast.
Derived random scalars must be nonzero. Production seed freshness and secrecy
remain wallet responsibilities.
The deterministic seeds in the native fixture are public test data.

The native lifecycle case registers two wallets, mints to the first wallet's
pending pool, sweeps, transfers to the second wallet's pending pool, then burns
two from the sender. Alice ends with five spendable, Bob with five pending and
zero spendable, and public supply is ten. It checks
decrypted balances with independent group arithmetic, public supply, memo Lists
and credit counters, then rejects a valid re-randomized old-ciphertext candidate which preserves
plaintext but differs from the ledger record. The same selected-3.2.1 native
sequence checks all five views, then self-moves one from Alice spendable to
Alice pending. Supply stays ten and Alice's credit epoch advances to two.
Clearing with epoch one rejects. Clearing with epoch two empties only Alice's
memo List and preserves the epoch and other ledger state. Self-transfer and
wrong-key clearing also reject. The expanded focused native case passes in 0.55 seconds.

The delegated-spend nonce preimage fits existing source operations:
`persistentHashVector32([seed, domain, owner, spender, toBytes32(epochNative)])`.
The pinned mixed record hashes four Bytes32 values followed by one canonical
Field, also 32 little-endian bytes. Alignment contributes no hash tags, so both
encodings produce the same 160-byte preimage. The delegated circuits now use this exact preimage. Readable witness
expressions share the existing typed `toBytes32` serialization route. [Native nested-map leaf deletion](native-map-remove.md) now supplies the
ledger primitive used for exact refund/replacement behavior.

The lifecycle then approves two for Bob and replaces the approval with three.
Replacement first refunds the prior two, so Alice ends with one spendable, one
pending and three escrowed. Bob keeps five pending and supply stays ten.
Independent group arithmetic checks both encrypted escrow copies and the owner
memo. Pending balances, credit counters and memo Lists stay unchanged. A valid
rerandomized old owner ciphertext rejects when used as the refund candidate.

Bob then transfers two from Alice's escrow into his pending pool and burns the
remaining one. Both escrow ciphertexts decrypt from three to one to zero, and
the owner memo carries each new remaining amount. Spend epochs advance from
one to two. Bob's pending balance reaches seven and his credit epoch reaches
two. Alice keeps one spendable and one pending, public supply ends at nine.
The delegated transfer consumes distinct spend/credit seed replies. Overspending
rejects with checked unsigned subtraction before native execution.

Deployment starts from explicitly configured initialized state, zero supply and
empty maps. Constructor/sealed metadata, nominal return layouts and composition remain open. All sixteen reference
circuit entrypoints are present; this does not establish constructor or full
ABI parity. The completed-contract localnet demonstration is still pending. Mint is the ungated
public-supply benchmark operation, not a production issuance policy. Native
acceptance here is checker evidence. No new keys, proofs or deployment were
created for this source milestone.
