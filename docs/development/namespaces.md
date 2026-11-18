# Canonical Noctium API

The Lean library lives under `Noctium/`. Import `Noctium.Frontend`, open the
`Noctium` scope and use `noctium_*` declarations. The parser implementation is
`Noctium.Frontend.Core`; the public facade adds readable private-state authoring.
The compiler executable is `noctium`, and its manifest is `noctium.json`.

The Rust package is `noctium-runtime`, imported as `noctium_runtime`. C and C++
applications use the `noctium_*.h` headers and `noctium_*` exported functions.
Rebuild native hosts against these headers. Local development artifacts use
`.noctium/`. Namespace compatibility aliases have been removed.

Retained proof and deployment records qualify their recorded source commits and
artifact bytes. Historical summaries identify the original record and digest.
They do not certify the renamed source tree. New exact-byte qualification belongs
to the [assurance backlog](https://github.com/awjreynolds/noctium/issues/21).
The rename includes schema fingerprints and wire markers, so current generated
fixtures must come from the current compiler and codecs.
