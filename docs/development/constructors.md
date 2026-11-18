# Constructors and sealed deployment cells

A contract may declare public constructor arguments and typed cell initializers:

```lean
sealed cell name : OpaqueString
sealed cell decimals : UInt 8
constructor(name_ : OpaqueString, decimals_ : UInt 8) where
  initialize name := name_
  initialize decimals := decimals_
end
```

The constructor builds fresh genesis state. Other state uses typed defaults,
including empty maps and Lists and zero Counters. Each sealed cell must have one
initializer. Constructor parameters and cell types must match. Missing, extra,
out-of-range or incorrectly typed arguments reject.

`construct_state(plan, arguments)` evaluates the compiler-emitted constructor.
The native deployment assembler uses this path when the artifact declares a
constructor. Its deployment `state` argument then contains constructor arguments.
Without a constructor, existing explicit state configuration remains supported.
`create_state` remains the low-level explicit state constructor/hydrator.

OpaqueString is deployment/host data, outside circuit `Ty`. Its cell contains one
raw UTF-8 FAB atom with Compress alignment. The codec preserves trailing U+0000,
which the generic byte-vector conversion would trim. Native compression uses
the UTF-8 byte count, including multibyte characters and trailing zero bytes.
`decode_opaque_string` validates the alignment and UTF-8 representation.

The compiler rejects entrypoint writes to sealed cells, including inactive
writes. The runtime rejects a prepared call which changes a sealed cell. Bundle
validation binds the constructor descriptor and sealed state schema to compiler
metadata. The ledger VM has no separate sealed-cell permission type.

Constructors execute off chain. This feature does not prove constructor
execution on the ledger. Deployment assurance must bind the source artifact,
constructor arguments and actual genesis state. This first constructor surface
supports public arguments and cell initializers, not private witness callbacks
or arbitrary initialization effects.

`tests/ConstructorMetadata.lean` and `runtime/tests/constructor_metadata.rs`
cover initialized metadata, UTF-8 with a trailing zero byte, immutable metadata,
argument rejection and a forged-plan mutation. Broader initialization and
state-preservation proofs remain separate work. The focused native case passed
in under 0.01 seconds.
