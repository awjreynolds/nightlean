# 03: Set the v1 circuit target boundary

Type: grilling

Status: resolved

## Question

Should v1 expose a circuit-focused Lean subset for current ledger 9, with supported operations derived from Midnight's ledger and proving interfaces?

The user confirmed a circuit-focused first version for current ledger 9 and directed the design to avoid treating Compact as the semantic boundary. Compact remains one possible artifact path. ZKIR and Impact VM are separate layers. See [Midnight target research](../../../docs/research/midnight-compact-runtime-scope.md).

## Blocked by

01: Map the deployable Midnight backend boundary.

## Answer

V1 is circuit-focused and targets current ledger 9. The supported language follows Midnight's ledger and proving interfaces. Compact does not define source semantics. Full general-purpose Lean remains out of scope. Exact workloads and backend artifact generation remain separate decisions.
