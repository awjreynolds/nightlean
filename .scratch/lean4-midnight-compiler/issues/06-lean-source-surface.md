# 06: Choose the Lean source surface

> Current source of truth: [public issue #2](https://github.com/awjreynolds/nightlean/issues/2). The current decision separates contract state transitions from circuit relations and keeps the source model general.

Type: research

Status: resolved

## Question

Given v1's private one-time claim workload and the decision to implement Nightlean in Lean 4, which source surface gives the compiler a narrow, well-typed boundary with useful source diagnostics? Compare a dedicated circuit declaration and elaborator with compiling ordinary Lean definitions and whitelisting their elaborated expressions. See [Lean frontend research](../../../docs/research/lean4-frontend-boundary.md).

## Answer

V1 uses a dedicated Lean `circuit` declaration and elaborator for the private one-time claim. The declaration marks private inputs, public inputs, outputs, and supported circuit operations explicitly. Elaboration checks types, preserves source locations, and produces a compiler-owned typed representation. Ordinary Lean definitions and constructs outside the declared subset are rejected.
