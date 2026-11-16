# 03: Set the v1 scope and compiler implementation language

> Current source of truth: [public issue #4](https://github.com/awjreynolds/nightlean/issues/4). Use GitHub for the latest decision and dependencies.

Type: grilling

Status: resolved

## Question

Should Nightlean itself be implemented in Lean 4 and compile a circuit-focused Lean subset for current ledger 9, with supported operations derived from Midnight's ledger and proving interfaces?

The user confirmed a circuit-focused first version for current ledger 9 and directed the design to avoid treating Compact as the semantic boundary. Compact remains one possible artifact path. ZKIR and Impact VM are separate layers. See [Midnight target research](../../../docs/research/midnight-compact-runtime-scope.md).

## Blocked by

01: Map the deployable Midnight backend boundary.

## Answer

Nightlean itself will be implemented in Lean 4. V1 targets current ledger 9 with a circuit-focused Lean source subset. Supported language features follow Midnight's ledger and proving interfaces. Compact does not define source semantics. Full general-purpose Lean remains out of scope. Exact workloads and backend artifact generation remain separate decisions.
