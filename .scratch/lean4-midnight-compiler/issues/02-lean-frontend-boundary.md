# 02: Identify Lean 4 frontend constraints for a compiler subset

Type: research

Status: resolved

## Question

Which official Lean 4 frontend or elaboration interfaces support accepting a restricted executable fragment, preserving source-level diagnostics, and rejecting unsupported constructs? Compare a Lean DSL or syntax extension with compiling elaborated definitions. Identify constraints relevant to a separate compiler project.

## Blocked by

None.

## Answer

A dedicated circuit declaration and elaborator provide the clearest restricted frontend. Lean's documented elaborators support custom syntax, environment-aware checking, and source-positioned diagnostics. Consuming ordinary Lean definitions remains possible, but requires a strict whitelist over elaborated core expressions and version pinning. See [lean4-frontend-boundary.md](../../../docs/research/lean4-frontend-boundary.md).
