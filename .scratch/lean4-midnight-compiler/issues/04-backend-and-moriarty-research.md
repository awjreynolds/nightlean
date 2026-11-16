# 04: Assess Moriarty and Midnight backend paths

Type: research

Status: resolved

## Question

How much does Moriarty's current native compiler overlap with Nightlean, and which backend path best fits a Lean 4 frontend for current ledger 9? Inspect its language profiles, direct ZKIR v3 lowerer, exposed CLI and APIs, plus proof and deployment maturity. Compare integrating with Moriarty, targeting ZKIR independently, and using Compact as an optional adapter. Use primary Midnight and Moriarty sources. Separate implemented capabilities from proposals and unverified gates, then recommend a direction.

The user supplied [Charles Hoskinson's Moriarty repository](https://github.com/CharlesHoskinson/Moriarty) as a relevant example. Its README describes a financial language and a native `moriarty/1` profile with a direct ledger-9 ZKIR v3 lowerer. The full proof and settlement path remains under development. Establish exact overlap and maturity before recommending Nightlean's backend.

## Answer

Nightlean should own its source semantics and typed circuit representation, derived from the selected ledger 9 and proving interfaces. Moriarty is a strong implementation reference and a backend candidate, but its financial frontend, version identifiers, and incomplete deployment evidence do not yet justify making it a fixed dependency. Keep Compact as an optional artifact adapter where it preserves Nightlean semantics. Before selecting a permanent lowerer, run the first chosen workload through compilation, proof generation and verification, artifact assembly, and deployment on current ledger 9 Preview. See [the Moriarty and backend research](../../../docs/research/moriarty-overlap.md).
