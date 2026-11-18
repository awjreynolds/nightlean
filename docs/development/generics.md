# Compile-time generics

Bounded type and natural specialization extends the Lean source helper
compiler. The pass turns one generic export into an ordinary monomorphic
`Noctium.Helpers.Program`. Existing helper analysis, component disclosure,
compilation and native lowering then process that concrete program.

The source API is `Noctium.Helpers.Specialization.Program`. It declares
parameter kinds, generic helper declarations, nominal generic structs,
transparent aliases and concrete exports. Generic calls use declaration IDs,
not names. A source export supplies ordered type and natural arguments. Runtime
values used as generic arguments fail with a Noctium diagnostic.

Aliases normalize to their underlying type. Struct specializations retain
nominal identity derived from the struct declaration and its full normalized
arguments. Structs with matching fields still have distinct IDs when their
source declarations differ. Generated helper names are collision-checked and
calls target those exact names, including when different type arguments have
the same flattened runtime shape.

Use `noctium_generic_circuit` to register one selected export as a regular
circuit:

```lean
import Noctium.Compiler
open scoped Noctium
open Noctium.Helpers.Specialization

private def genericProgram : Program := ...

noctium_generic_circuit concreteCircuit from genericProgram entry "export"
```

The frontend stores the generated concrete program and its versioned signature
sidecar. Compiler checks run again over that same program during compilation.
The additive sidecar uses schema version 1 and writes natural values and source
or generated identity integers as canonical decimal strings. Existing
`noctium.json` and aggregate schemas stay unchanged. The sidecar records typed
witness signatures as compile-time metadata. [General typed witness execution](https://github.com/awjreynolds/noctium/issues/62)
is separate runtime work.

Specialization preflights source size and nesting, charges clone costs before
substitution, caches instances by structural declaration ID and ordered
normalized arguments, and enforces hard limits on helper and type instances,
retained composite declarations and layout nodes, work, argument count, depth
and natural values. Active recursive or growing specializations fail with a
Noctium cycle diagnostic. These are Noctium implementation caps,
not Compact language limits. [Module visibility](https://github.com/awjreynolds/noctium/issues/47)
and [finite iteration](https://github.com/awjreynolds/noctium/issues/48) remain separate work.

## Published qualification

The implementation is commit `396c514de223c9cda7f6f49a4525c9531ccfe1ba`.
All 74 selected compiler, proof, tool and fixture Git blobs and executable modes
match the independently tested snapshot. The full compiler/source-proof check
passed, including the new lexical-scope, active-instance, depth and normalized-type
resource regressions. Independent compilation of both profiles produced identical
relations and signature sidecars. Six official 3.2.1 checker cases passed.

[Qualification evidence](../../tests/generics/qualification-evidence.json) records
source, checker, relation, key and proof hashes. The two exact retained relations
produced native proofs which the worker observed the service self-verify.
Independent qualification checked relation identity and raw witnesses, without
rerunning cryptographic proof verification. This is compile-time specialization
evidence, with no general specialization-preservation theorem or ledger-deployment
claim.

## Focused checks

Lean cases cover kind and arity errors, monomorphic exports, alias and nominal
identity, nested type and natural environments, cache reuse, growing cycles,
resource rejection before cloning, private/provider disclosure, and sidecar
roundtrips:

```sh
lake env lean tests/GenericSpecialization.lean
lake env lean tests/generics/Native.lean
```

`tests/generics/Native.lean` specializes a bounded scalar addition helper at
`N = 15` and `N = 255`. Compile both circuits to the pinned native ZKIR profile
in a temporary directory, then run six valid and rejecting cases through the
official 3.2.1 checker:

```sh
OUT=/private/tmp/noctium-generic46
lake exe noctium compile tests/generics/Native.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json --output "$OUT"
node scripts/zkir/check-scalar-cases.mjs "$OUT" \
  /private/tmp/noctium-zkir321-wasm/package/midnight_zkir_wasm_fs.js \
  tests/generics/cases.json
```

Both specializations have passed native key generation and proof through the
loopback proof service. The service self-verifies each proof. After key
generation, repeat either proof in a temporary output directory:

```sh
mkdir -p "$OUT/keys"
MIDNIGHT_PP=/private/tmp/noctium-proof-params \
  /private/tmp/noctium-native-zkir-321/bin/zkir compile \
  "$OUT/genericAddSmall.zkir" \
  "$OUT/keys/genericAddSmall.prover" "$OUT/keys/genericAddSmall.verifier"
MIDNIGHT_PP=/private/tmp/noctium-proof-params \
  /private/tmp/noctium-native-zkir-321/bin/zkir compile \
  "$OUT/genericAddWide.zkir" \
  "$OUT/keys/genericAddWide.prover" "$OUT/keys/genericAddWide.verifier"
node tests/generics/prove-native.mjs "$OUT" \
  /private/tmp/noctium-zkir321-wasm/package/midnight_zkir_wasm_fs.js genericAddSmall
node tests/generics/prove-native.mjs "$OUT" \
  /private/tmp/noctium-zkir321-wasm/package/midnight_zkir_wasm_fs.js genericAddWide
```

The runner checks the official 3.2.1 preimage, uses the native service at
`127.0.0.1:16300`, and writes proof bytes only under `OUT`. It submits no ledger
transaction. This run generated k=7 and k=6 keys from the exact two emitted
relations. The native service self-verified a 3,468-byte proof for each one.
