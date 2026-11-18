# Explicit native copy

Use `copyValue(expr)` in a direct Lean circuit or contract entrypoint when
you want a native ZKIR alias. The expression retains its type and value.
Ordinary source bindings still reuse their existing operands.

The compiler emits `copy` for each existing native operand. A byte string
keeps its current leaf or chunk representation, including zero operands
for an empty byte string. The Rust execution plan evaluates the underlying
expression directly because copying changes neither its value nor its
effects.

The independent producer requires a defined operand or canonical Native
immediate and a fresh result identifier. The result inherits the whole
operand fact, including bounds, symbolic identity and typed validity. Copy
does not approve disclosure. The compiler checks the same private origins
before and after a copy.

The [source fixture](../../tests/NativeCopy.lean) copies Native, Bool, byte
and Secp256k1 base field values. The native checker accepts both guard
branches, preserves the copied results and rejects an altered equality
operand. The producer tests reject use before definition, redefinition and
an attempt to treat a copy of an unconstrained input as range checked.

This completes scoped registration of all 40 non-deprecated instruction names
on the pinned profile. The inventory also lists seven deprecated upstream names. The result covers direct source authoring and native
checking. Readable helper authoring, exhaustive type qualification and fresh
proof generation for this fixture remain open.
