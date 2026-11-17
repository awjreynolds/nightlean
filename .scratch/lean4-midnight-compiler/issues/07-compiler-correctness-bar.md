# 07: Set the compiler correctness bar

> Current source of truth: [public issue #5](https://github.com/awjreynolds/noctium/issues/5). Use GitHub for the latest decision and dependencies.

Type: research

Status: resolved

## Question

What correctness and assurance evidence should v1 require for the supported Lean subset and its generated Midnight artifacts? Separate internal compiler transformations, the external ZKIR/proving boundary, and public-network release claims.

## Answer

V1 has a layered assurance bar. Define reference semantics in Lean and prove internal typed-IR transformations preserve them. Differentially validate emitted ZKIR, proof generation and verification, contract artifacts, and the private-claim state transition against the reference semantics and exact ledger 9 toolchain. Reject unsupported source before code generation. Require independent security review and successful Preview integration before production. Do not claim end-to-end formal verification until proofs cover ZKIR, proving, and contract execution as well as Lean compiler passes.
