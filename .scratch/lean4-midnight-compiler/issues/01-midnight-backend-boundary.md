# 01: Map the deployable Midnight backend boundary

> Current source of truth: [public issue #3](https://github.com/awjreynolds/noctium/issues/3). Use GitHub for the latest decision and dependencies.

Type: research

Status: resolved

## Question

Which documented path lets a non-Compact frontend produce a contract that deploys and runs on Midnight ledger 9? Compare generating Compact source and invoking the official toolchain with lowering directly to ZKIR or Impact VM artifacts. Identify the required artifacts, public interfaces, version constraints, and compatibility risks using official Midnight sources.

## Blocked by

None.

## Answer

Midnight documents a complete build and deployment path starting from Compact source. The ZKIR repository documents compilation of `.zkir` files into prover and verifier keys, but reviewed sources do not document a complete direct-ZKIR path that also produces contract bindings and the deployment bundle. The Compact-source route is a recommendation, not a user-approved implementation decision. See [midnight-backend-boundary.md](../../../docs/research/midnight-backend-boundary.md).
