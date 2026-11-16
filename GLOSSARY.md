# Nightlean glossary

This glossary defines Nightlean's source, compiler, and Midnight target terms.

## Language and target

**Compact**:
Midnight's smart-contract language for circuits and ledger interactions.

**ZKIR**:
Midnight's zero-knowledge intermediate representation for contract circuits. The official term is ZKIR version 3, not “zkR3”.
_Avoid_: zkR, zkR3

**Impact VM**:
Midnight's on-chain execution environment, separate from ZKIR.
_Avoid_: ZKIR runtime

**Ledger era**:
A versioned Midnight network compatibility target, such as ledger 9.
_Avoid_: ZKIR version

**Circuit-focused Lean subset**:
The supported portion of Lean 4 for expressing Midnight circuit relations and contract transitions. The first workload bounds the first release, while the compiler's typed core and target model stay open to additional ledger-backed capabilities. Its feature boundary follows Midnight's ledger and proving interfaces, not another source language.
_Avoid_: full Lean compiler

**Circuit relation**:
A computation whose constraints connect public inputs, private witnesses, and public outputs. The relation defines what the proof establishes. It does not define which ledger state changes follow from an accepted proof.

**Witness**:
A private value supplied when constructing a proof. Witness values and private intermediate values must stay out of public outputs unless the program explicitly reveals a value.

**Public input**:
A value bound into the proof or contract call and available to the verifier or ledger execution.

**Circuit output**:
A value computed by a circuit relation and exposed for proof verification or contract execution. Output visibility must be explicit.

**Contract state effect**:
A declared state read or write performed by a contract transition around a verified circuit relation. State effects are modeled separately from circuit constraints.

**Contract-call transcript**:
The public call data and proof-bound values that Midnight validates when deciding whether to accept a contract transaction. Nightlean must bind declared public inputs and outputs to the target ledger's transcript format.

**Nullifier**:
A value derived from private claim data and bound into the public proof or call. Ledger state records spent nullifiers to reject reuse.

**Commitment**:
A cryptographic value that binds data while hiding the committed private values. A public Merkle root can commit to a set of eligible claims.

**One-time claim**:
The first Nightlean vertical-slice workload. A claimant proves membership using private eligibility data and a private Merkle path, supplies a public root, and publishes a nullifier that ledger state marks as spent.

**Target profile**:
A versioned set of Midnight ledger, ZKIR, proving, proof-server, and on-chain runtime interfaces that a Nightlean build supports. Target profile capabilities are separate from source-language semantics.

**Supported capability**:
A Nightlean operation with evidence at four boundaries: compiler implementation, target proving or verifier acceptance, contract artifact integration, and transaction execution on the named profile. Presence in a library or ZKIR source alone is not sufficient.
