# 03: Set the v1 Compact and ZKIR boundary

Type: grilling

Status: claimed

## Question

Should v1 expose a circuit-focused Lean subset that lowers through the documented Compact language and runtime for one pinned ledger era, aim for full Compact feature parity, or include lower-level ZKIR or Impact VM capabilities beyond Compact?

The current recommendation is a circuit-focused subset aligned with the documented Compact interface for ledger 9. Compact toolchain 0.36.0 generates ZKIR version 3, but ZKIR and the Impact VM are separate layers. The documented build pipeline accepts Compact source and generates deployable artifacts. See [the current evidence](../../../docs/research/midnight-compact-runtime-scope.md) and [the backend boundary research](../../../docs/research/midnight-backend-boundary.md).

## Blocked by

01: Map the deployable Midnight backend boundary.
