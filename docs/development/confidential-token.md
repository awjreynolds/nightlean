# Confidential-token integration

`examples/openzeppelin/ConfidentialToken.lean` adapts the registration, credit, sweep, transfer, burn and query paths from OpenZeppelin's confidential fungible token at
revision `f85f1a23685c6bbedfc8c2589ae3aa128aff7c46`. Noctium compiles the source
directly to native ZKIR and ledger operations. This milestone covers ten
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
The views expose supply, registration, spendable/pending ciphertexts and account
ID computation. Missing ciphertext entries return curve-identity encrypted zero.
Ciphertext results use named typed `c1` and `c2` point components; nominal
composite ABI layouts remain separate work.

| State | Representation |
| --- | --- |
| encryptionKeys | Account ID to two Native key coordinates |
| balances, pending | Account ID to four Native ciphertext coordinates |
| memos | Account ID to a List of three-Native ECDH memo records |
| creditEpochs | Account ID to a native u64 Counter |
| initialized | Public initialization precondition |
| totalSupply | Public UInt128 supply |

The source takes candidate IDs, points and ciphertext coordinates as circuit
inputs. It checks account IDs against private secrets, keys against registered
keys, and every candidate ciphertext against actual ordered ledger reads before
writing. A candidate input is not trusted state. The account ID is returned as
a typed Bytes32 result bound to the native output commitment.

Private account and encryption secrets come from wallet-scoped native witness
reads. A typed callback supplies a UInt128 plaintext claim indexed by the sender's
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
plaintext but differs from the ledger record. The one selected-3.2.1 native
sequence also checks all five views and passes in 0.20 seconds.

Deployment starts from explicitly configured initialized state, zero supply and
empty maps. Constructor/sealed metadata, the remaining six reference entrypoints, escrow/allowance,
memo clearing, nominal return layouts and composition remain open. Mint is the ungated
public-supply benchmark operation, not a production issuance policy. Native
acceptance here is checker evidence. No new keys, proofs or deployment were
created for this source milestone.
