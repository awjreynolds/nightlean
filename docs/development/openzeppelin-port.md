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
| Dynamic map-value reads | Balances, registered keys and allowances | Scalar reads compile from Lean to native two-part index paths. A focused 3.2.1 example passes read-after-write and rejects a tampered read. Missing keys fail. |
| Multi-entrypoint calls on current state | Registration, transfer and supply calls on one deployed contract | Bundle collection and retained-deployment assembly exist; proof/client handoff remains open in issue 67. |
| Guarded native execution | Missing accounts, balance checks and conditional updates | Host control exists; native guard/effect integration remains open in issue 43. |
| Composite ledger values and byte keys | Account identifiers, encrypted balances and escrow records | Checked composite values exist; general aggregate ledger effects remain open. |
| Jubjub and cryptographic source operations | ElGamal balances, key registration and account identifiers | Native inventory exists; safe Lean exposure remains incomplete. |
| Lean port integration | Register, mint, transfer, approve, transferFrom and burn | Build after the required feature paths work. |

The complete 47-instruction, 15-type native inventory remains the wider target.
The token workload does not exercise every native instruction.

## Minimum checks

Compile each changed feature group. Run one focused native example and one
targeted rejection case where its semantics need one. Reuse existing evidence.
Run one integrated localnet demonstration at the completed-port milestone.
Additional proofs, repeated export audits, broad regression campaigns and
duplicate deployments stay in the assurance backlog.

Historical formal qualification remains attached to its recorded source commit.
New POC features do not inherit those proof claims automatically.
The map-read extension needs corresponding changes in `GenericStateOps.lean`,
`GenericStateEffectStep.lean` and `GenericStateConverseEffectStep.lean` before
the generic-state proof suite covers the extended compiler. That work belongs
to the [assurance backlog](https://github.com/awjreynolds/noctium/issues/21).
