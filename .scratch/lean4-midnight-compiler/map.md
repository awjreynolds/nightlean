# Lean 4 compiler for Midnight

## Destination

A deployable compiler for a defined subset of Lean 4 programs used to build Midnight smart-contract ZK circuits. The supported language, target artifacts, compatibility profile, and correctness evidence are explicit and validated.

## Notes

- The user requested a working Lean 4 subset compiler for Midnight ZK circuit construction.
- This map follows the Wayfinder process. Implementation starts after the route is clear.
- The repo has no remote. Use the local Markdown tracker under `.scratch/`.
- The user prefers an MIT license if a public repo becomes necessary. No public repo is needed for this map.
- Current Midnight version research is in [midnight-compact-runtime-scope.md](../../docs/research/midnight-compact-runtime-scope.md).
- Backend integration evidence is in [midnight-backend-boundary.md](../../docs/research/midnight-backend-boundary.md).
- Lean frontend evidence is in [lean4-frontend-boundary.md](../../docs/research/lean4-frontend-boundary.md).

## Decisions so far

- [Map the deployable Midnight backend boundary](issues/01-midnight-backend-boundary.md): V1 should generate Compact source and use the pinned official toolchain to produce deployable artifacts. See [the research report](../../docs/research/midnight-backend-boundary.md).
- [Identify Lean 4 frontend constraints for a compiler subset](issues/02-lean-frontend-boundary.md): A dedicated circuit declaration and elaborator define a narrow checked source boundary with diagnostics. See [the research report](../../docs/research/lean4-frontend-boundary.md).

## Not yet specified

- Compiler packaging, user workflow, and support for future ledger eras.

## Out of scope

- Compiling arbitrary general-purpose Lean 4 programs that do not fit the Midnight contract and circuit model.
