# 03: Set the v1 Compact and ZKIR boundary

Type: grilling

## Question

Should v1 expose only a circuit-focused Lean subset that lowers through the documented Compact language and runtime for one pinned ledger era, aim for full Compact feature parity, or target lower-level ZKIR or Impact VM capabilities outside Compact?

The current recommendation is a circuit-focused subset aligned with the documented Compact interface for ledger 9. Compact toolchain 0.36.0 generates ZKIR version 3, but ZKIR and the Impact VM are separate layers. See [the current evidence](../../../docs/research/midnight-compact-runtime-scope.md).

## Blocked by

01: Map the deployable Midnight backend boundary.
