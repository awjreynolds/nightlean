# 02: Identify Lean 4 frontend constraints for a compiler subset

> Current source of truth: [public issue #6](https://github.com/awjreynolds/noctium/issues/6). Use GitHub for the latest decision and dependencies.

Type: research

Status: resolved

## Question

Which official Lean 4 frontend or elaboration interfaces support accepting a restricted executable fragment, preserving source-level diagnostics, and rejecting unsupported constructs? Compare a Lean DSL or syntax extension with compiling elaborated definitions. Identify constraints relevant to a separate compiler project.

## Blocked by

None.

## Answer

Lean's documented elaborators support custom syntax, environment-aware checking, and source-positioned diagnostics. Consuming ordinary Lean definitions requires a strict whitelist over elaborated core expressions and version pinning. A dedicated circuit declaration is a recommendation, not a user-approved source-interface decision. See [lean4-frontend-boundary.md](../../../docs/research/lean4-frontend-boundary.md).
