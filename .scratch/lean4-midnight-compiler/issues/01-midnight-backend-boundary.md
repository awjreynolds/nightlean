# 01: Map the deployable Midnight backend boundary

Type: research

Status: resolved

## Question

Which documented path lets a non-Compact frontend produce a contract that deploys and runs on Midnight ledger 9? Compare generating Compact source and invoking the official toolchain with lowering directly to ZKIR or Impact VM artifacts. Identify the required artifacts, public interfaces, version constraints, and compatibility risks using official Midnight sources.

## Blocked by

None.

## Answer

For v1, generate Compact source from the Lean subset and invoke the pinned official Compact toolchain. Official documentation describes the full build and deployment artifact path. The ZKIR repository documents circuit compilation into keys, but the reviewed sources do not document a complete direct-ZKIR route that also produces the contract bindings and deployment bundle. See [midnight-backend-boundary.md](../../../docs/research/midnight-backend-boundary.md).
