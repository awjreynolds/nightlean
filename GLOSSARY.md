# Lean 4 to Midnight compiler

This context defines the terms used for a Lean compiler targeting Midnight smart-contract circuits.

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
The supported portion of Lean 4 for expressing computations used in Midnight contract circuits. Its boundary follows the selected Midnight ledger and proving interfaces, not the syntax or feature list of another source language.
_Avoid_: full Lean compiler
