# Nightlean Wayfinder map snapshot

The canonical, current map is [public GitHub issue #1](https://github.com/awjreynolds/nightlean/issues/1). GitHub Issues is the source of truth for ticket descriptions, status, child links, and blocking dependencies. The local issue drafts in this directory are historical planning snapshots.

## Current direction

- Implement the compiler, elaboration, typed IR, passes, and primary lowering in Lean 4.
- Target current Midnight ledger 9 for v1.
- Keep circuit relations, witness providers, contract state effects, and transaction bindings separate in the compiler model.
- Use a private one-time claim as the first vertical slice. Do not design the IR around this workload.
- Derive supported features from ledger, proving, and contract execution interfaces. Compact remains an optional semantics-preserving adapter, never the feature boundary.
- Qualify any capability through the pinned compile, proof, artifact, and transaction path before claiming support.

## Public decision and research tickets

- [#2 Extensible Lean contract and circuit source surface](https://github.com/awjreynolds/nightlean/issues/2)
- [#3 Deployable backend boundary](https://github.com/awjreynolds/nightlean/issues/3)
- [#4 V1 scope and compiler language](https://github.com/awjreynolds/nightlean/issues/4)
- [#5 Correctness and assurance bar](https://github.com/awjreynolds/nightlean/issues/5)
- [#6 Lean frontend constraints](https://github.com/awjreynolds/nightlean/issues/6)
- [#7 Moriarty and backend comparison](https://github.com/awjreynolds/nightlean/issues/7)
- [#8 First workload](https://github.com/awjreynolds/nightlean/issues/8)
- [#11 Native claim primitives](https://github.com/awjreynolds/nightlean/issues/11)
- [#12 Witness, proof, and state boundaries](https://github.com/awjreynolds/nightlean/issues/12)
- [#13 Documented ledger 9 interfaces](https://github.com/awjreynolds/nightlean/issues/13)
- [#14 ZKIR source capability audit](https://github.com/awjreynolds/nightlean/issues/14)

## Open qualification and implementation issues

- [#9 First Lean-to-ZKIR vertical slice](https://github.com/awjreynolds/nightlean/issues/9), blocks [#10 artifact route](https://github.com/awjreynolds/nightlean/issues/10).
- [#15 Lake package and CLI](https://github.com/awjreynolds/nightlean/issues/15).
- [#16 Extensible typed circuit and contract IR](https://github.com/awjreynolds/nightlean/issues/16).
- [#17 Contract and circuit elaborators](https://github.com/awjreynolds/nightlean/issues/17).
- [#18 Claim primitives and canonical encodings](https://github.com/awjreynolds/nightlean/issues/18).
- [#19 Lean lowering to ledger 9 ZKIR](https://github.com/awjreynolds/nightlean/issues/19).
- [#20 Witness, proof, and contract state integration](https://github.com/awjreynolds/nightlean/issues/20).
- [#21 Semantic-preservation and conformance checks](https://github.com/awjreynolds/nightlean/issues/21).
- [#22 Private claim on Preview](https://github.com/awjreynolds/nightlean/issues/22).
- [#23 Independent security review](https://github.com/awjreynolds/nightlean/issues/23).
- [#24 User and target-profile documentation](https://github.com/awjreynolds/nightlean/issues/24).
- [#25 Post-v1 ledger 9 capability backlog](https://github.com/awjreynolds/nightlean/issues/25).

## Research reports

Current cited reports live in [`docs/research/`](../../docs/research/). Use linked GitHub issues for current decisions and execution order.
