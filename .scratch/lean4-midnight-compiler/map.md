# Lean 4 compiler for Midnight

## Destination

A deployable compiler for a defined subset of Lean 4 programs used to build Midnight smart-contract ZK circuits. The supported language, target artifacts, compatibility profile, and correctness evidence are explicit and validated.

## Notes

- The user requested a working Lean 4 subset compiler for Midnight ZK circuit construction.
- This map follows the Wayfinder process. Implementation starts after the route is clear.
- The canonical tracker is GitHub Issues in `awjreynolds/nightlean`. These local files are a migration snapshot.
- The repository uses the MIT license.
- Nightlean's compiler implementation itself is Lean 4, and its source input is a defined Lean 4 subset.
- Do not use Compact as the definition of Nightlean's source semantics. Evaluate backend choices against Midnight's current ledger and proving interfaces.
- Assess Moriarty as an adjacent financial language and direct ZKIR implementation before choosing Nightlean's backend.
- Current Midnight version research is in [midnight-compact-runtime-scope.md](../../docs/research/midnight-compact-runtime-scope.md).
- Backend integration evidence is in [midnight-backend-boundary.md](../../docs/research/midnight-backend-boundary.md).
- Moriarty overlap and backend comparison are in [moriarty-overlap.md](../../docs/research/moriarty-overlap.md).
- Lean frontend evidence is in [lean4-frontend-boundary.md](../../docs/research/lean4-frontend-boundary.md).

## Decisions so far

- [Map the deployable Midnight backend boundary](issues/01-midnight-backend-boundary.md): Official docs describe the complete contract artifact path from Compact source; this documents one available path, not a required Nightlean target. See [the research report](../../docs/research/midnight-backend-boundary.md).
- [Identify Lean 4 frontend constraints for a compiler subset](issues/02-lean-frontend-boundary.md): Lean supports custom elaborators with environment-aware checks and source-positioned diagnostics; ordinary Lean definitions need a strict expression whitelist. See [the research report](../../docs/research/lean4-frontend-boundary.md).
- [Set the v1 scope and compiler implementation language](issues/03-v1-capability-boundary.md): Nightlean itself is implemented in Lean 4; v1 is a circuit-focused subset for ledger 9, bounded by Midnight's ledger and proving interfaces.
- [Assess Moriarty and Midnight backend paths](issues/04-backend-and-moriarty-research.md): Nightlean's compiler and primary lowering are Lean code; use Moriarty as a reference and validate the final artifact route through an end-to-end ledger 9 spike.
- [Choose the first contract workloads](issues/05-first-contract-workloads.md): The first vertical slice is a private one-time claim with a public commitment or root, a nullifier, and ledger state that prevents reuse.
- [Choose the Lean source surface](issues/06-lean-source-surface.md): V1 uses a dedicated, elaborated Lean `circuit` declaration and rejects ordinary Lean constructs outside the declared subset.
- [Set v1 compiler correctness and assurance bar](issues/07-compiler-correctness-bar.md): Prove internal typed-IR transformations, validate the ZKIR/proving boundary and Preview path, and require an independent review before production.

## Not yet specified

- Compiler packaging and user workflow, and support for future ledger eras.

## Out of scope

- Compiling arbitrary general-purpose Lean 4 programs that do not fit the Midnight contract and circuit model.
