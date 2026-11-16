# Lean 4 frontend options for a restricted compiler

Research ticket: [02: Identify Lean 4 frontend constraints for a compiler subset](../../.scratch/lean4-midnight-compiler/issues/02-lean-frontend-boundary.md)

Checked 2026-11-16 against the Lean reference manual and the Lean 4 repository.

## Verified facts

- Lean processes source through parsing, macro expansion, elaboration, kernel checking, and compilation. Elaboration turns user syntax into expressions in Lean's core type theory. The stages interleave as Lean parses and elaborates top-level commands. [Elaboration and Compilation](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
- Lean's parser is extensible. Syntax declarations add productions, while macros transform `Syntax` into `Syntax`. The macro monad does not expose the environment, local context, or unification. [Syntax extensions](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Defining-New-Syntax/) [Macros](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Macros/)
- Term elaborators receive `Syntax` plus an optional expected type and return a core `Expr`. Command elaborators process syntax with access to the environment and can add declarations. Lean's reference manual documents both `elab_rules` and `term_elab` / `command_elab` registration. [Elaborators](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Elaborators/)
- The documented command elaboration API supports environment queries such as `getEnv`; `logInfoAt` and `throwErrorAt` attach messages to input syntax. The Lean parser records source positions on tokens, and synthetic syntax can retain source spans back to the original input. [Elaborators](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Elaborators/) [Source positions](https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Defining-New-Syntax/)
- Lean stores interactive elaboration metadata in info trees, which associate core expressions and other information with original syntax. This association is separate from the kernel expression itself. [Elaboration and Compilation, Info Trees](https://lean-lang.org/doc/reference/latest/Elaboration-and-Compilation/)
- Lean's `Lean.Elab.Frontend` implementation owns parser and command state and processes source by parsing commands and invoking command elaboration. This is implementation evidence, not a compatibility promise for a separately versioned compiler. [Lean.Elab.Frontend source](https://github.com/leanprover/lean4/blob/master/src/Lean/Elab/Frontend.lean)

## Implications for the compiler

- A dedicated circuit command or term DSL gives the compiler a small syntax and elaboration boundary. An elaborator can type-check inputs and construct an explicit compiler-owned representation. This avoids treating every core Lean construct as a target-language feature. This is an architectural inference from Lean's syntax and elaborator extension points.
- Consuming existing Lean definitions offers Lean's normal parsing, elaboration, and kernel checking, but the compiler still needs a strict whitelist over the resulting core expressions, referenced declarations, and types. Surface notation and macro expansions have already been elaborated, so preserve syntax or info-tree references if diagnostics need to point to user-written code. This is an architectural inference from Lean's pipeline and info-tree model.
- Macros alone are a poor place for type-directed validation or environment-dependent compilation because the macro monad lacks the environment, local context, and unification. Use an elaborator for such checks. This follows from the documented macro and elaborator capabilities.
- The public manual documents syntax and elaborator extension points. The standalone `Frontend` module exposes lower-level parser/command machinery in source, but the source does not promise cross-version API stability. A compiler that embeds those internals should pin Lean and test each supported version. This is an architectural inference from the distinction between reference-manual interfaces and implementation source.

## Recommendation

Prototype a Lean package extension with a dedicated circuit declaration and elaborator first. Keep the accepted AST explicit and small, retain original syntax spans for diagnostics, and reject unsupported constructs at the elaboration boundary. Consider traversing arbitrary Lean definitions only if the required workloads demand ordinary Lean syntax; if selected, whitelist core expressions and pin the Lean version.
