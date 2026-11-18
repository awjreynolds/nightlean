# Lean module identity and views

`Noctium.Modules` provides the bounded compile-time core for Noctium module
composition. Registration receives the full Lean `Name` for each source
module. A user-facing alias or import path does not replace that identity.

An instance key contains the source `Name` and its ordered normalized type or
natural arguments. Equal keys share one expansion. Different source names or
arguments produce distinct member identities, even when their runtime shapes
match. Re-exports and selective imports hold references to the original member
identity. They do not copy state fields or grant access to private members.

The expansion API accepts a registry of pure module definitions:

```lean
import Noctium.Modules
open Noctium.Modules

private def registry : Registry := ...
def result := expand registry `Demo.Entry []
```

Definitions list source members, imports, selections, and exports. Each member
has a registration ordinal, source name, kind, visibility, and source span.
Imports name the exact target module identity and may pass concrete normalized
arguments or forward parameters declared by the importing module. Exports may
reference local public members or selected names from imported views.

A circuit or witness member may carry a `SourceExportRef`, which points to an
original generic helper program constant, export name, and ordered arguments.
Expansion resolves module parameters into a `ResolvedSourceExport`. A view
stores only the member identity, so compiler checks and typed witness signature
metadata continue to resolve through the original source constant.

Modules with ledger behavior also declare typed state members and entrypoint
templates. A template points to a circuit member and uses `StateTarget` values
for reads and writes. Expansion resolves those references through the module's
own members or selected import views. `Expansion.contractPlan` deduplicates
state by full member identity, assigns canonical field names, resolves entry
aliases, and groups helper requests by exact source program. The frontend then
specializes each group with the issue46 batch session, checks the concrete
program, attaches the compiled circuits, and validates an ordinary
`Noctium.Contract`.

State schemas support fixed scalar types, type parameters that specialize to a
scalar, and unsigned bounds supplied by natural parameters. Expansion resolves
the schema for each exact module key before checking effects. Aggregate state
types fail with a source diagnostic. `writeCellOutput` takes its type from the
resolved cell and names a circuit output; ordinary contract validation checks
that output's type against the selected circuit.

The expansion checks module arity and argument kinds, unknown modules and
exports, private-member exports, duplicate source identities, import cycles,
and configurable work limits. It charges instance and node budgets before
expanding a module. It bounds normalized type nodes before canonical key
encoding. Canonical keys encode `Name` constructors, component and argument
boundaries, full normalized types, and decimal natural values. A fixed digest
provides stable field names. The expansion retains each exact structural key
and rejects digest collisions before producing output. Digests are identifiers,
not cryptographic authority.

`Expansion.stateFieldName` derives a field name from the originating module
instance and member ordinal. An alias view returns the same field name as the
source member. `resolveImport` and `resolveExport` return references with the
same source identity, so visibility and disclosure analysis can keep using the
original member metadata.

This module is the pure expansion layer. Frontend and compiler registration
must re-expand the registered root and use fresh concrete specialized helper
programs, source spans, disclosure origins, and typed witness signature
metadata during compilation. The issue46 batch session ensures export order
does not affect generated identities. General cross-contract calls are
separate issue50 work. Runtime execution of general typed witness functions is
issue62 and is not provided by module expansion.

## Focused checks

Run the pure expansion cases and deterministic source CLI fixture with:

```sh
bash tests/modules/check.sh
```

`tests/Modules.lean` covers structural source identity, alias and re-export
identity, same-key cache reuse, distinct generic instances, nested argument
forwarding, kind and arity rejection, private visibility, import cycles, and
instance/type-node limits. It also exercises the issue46 batch specialization
API, which processes one selected export set in sorted name order while sharing
its helper and type caches.

`tests/modules/Native.lean` registers a generic module whose helper and state
are specialized with natural and scalar type arguments. Two aliases for
`(2, Native)` must share one state field and one circuit. `(3, UIntRange<256>)`
must receive its own identities and state type. `tests/modules/check.sh`
compiles the source twice for the pinned
3.2.1 target, compares every emitted byte, and checks those relationships in
the manifest. This checks source emission and module identity. Multi-entrypoint
ledger acceptance remains the separate issue67 qualification.

The compiler re-expands each module contract from its registered source
constants during inspection. It then re-runs generic specialization,
component disclosure, witness compilation, and contract validation. Cached
generated constants provide stable source names, while fresh output supplies
the program, circuit, contract, witness, and signature data used by compilation.
