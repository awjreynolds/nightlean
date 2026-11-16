# Lean 4 compiler for Midnight

## Destination

A deployable compiler for a defined subset of Lean 4 programs used to build Midnight smart-contract ZK circuits. The supported language, target artifacts, compatibility profile, and correctness evidence are explicit and validated.

## Notes

- The user requested a working Lean 4 subset compiler for Midnight ZK circuit construction.
- This map follows the Wayfinder process. Implementation starts after the route is clear.
- The canonical tracker is GitHub Issues in `awjreynolds/nightlean`. These local files are a migration snapshot.
- The repository uses the MIT license.
- Do not use Compact as the definition of Nightlean's source semantics. Evaluate backend choices against Midnight's current ledger and proving interfaces.
- Assess Moriarty as an adjacent financial language and direct ZKIR implementation before choosing Nightlean's backend.
- Current Midnight version research is in [midnight-compact-runtime-scope.md](../../docs/research/midnight-compact-runtime-scope.md).
- Backend integration evidence is in [midnight-backend-boundary.md](../../docs/research/midnight-backend-boundary.md).
- Lean frontend evidence is in [lean4-frontend-boundary.md](../../docs/research/lean4-frontend-boundary.md).

## Decisions so far

- [Map the deployable Midnight backend boundary](issues/01-midnight-backend-boundary.md): Official docs describe the complete contract artifact path from Compact source; this documents one available path, not a required Nightlean target. See [the research report](../../docs/research/midnight-backend-boundary.md).
- [Identify Lean 4 frontend constraints for a compiler subset](issues/02-lean-frontend-boundary.md): Lean supports custom elaborators with environment-aware checks and source-positioned diagnostics; ordinary Lean definitions need a strict expression whitelist. See [the research report](../../docs/research/lean4-frontend-boundary.md).
- [Set the v1 circuit target boundary](issues/03-v1-capability-boundary.md): V1 is circuit-focused for ledger 9; Midnight's ledger and proving interfaces define the feature boundary.

## Not yet specified

- Compiler packaging, user workflow, and support for future ledger eras.

## Out of scope

- Compiling arbitrary general-purpose Lean 4 programs that do not fit the Midnight contract and circuit model.
