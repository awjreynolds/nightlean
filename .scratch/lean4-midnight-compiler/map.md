# Lean 4 compiler for Midnight

## Destination

A deployable compiler for a defined subset of Lean 4 programs used to build Midnight smart-contract ZK circuits. The supported language, target artifacts, compatibility profile, and correctness evidence are explicit and validated.

## Notes

- The user requested a working Lean 4 subset compiler for Midnight ZK circuit construction.
- This map follows the Wayfinder process. Implementation starts after the route is clear.
- The repo has no remote. Use the local Markdown tracker under `.scratch/`.
- The user prefers an MIT license if a public repo becomes necessary. No public repo is needed for this map.
- Current Midnight version research is in [midnight-compact-runtime-scope.md](../../docs/research/midnight-compact-runtime-scope.md).

## Decisions so far

## Not yet specified

- The Lean source boundary: embedded DSL, restricted elaborated Lean terms, or another interface.
- Initial contract workloads and which private/public data, state, and circuit operations they require.
- The correctness claim for compiled circuits and the evidence required before deployment.
- Compiler packaging, user workflow, and how future ledger-era support will be versioned.

## Out of scope

- Compiling arbitrary general-purpose Lean 4 programs that do not fit the Midnight contract and circuit model.
