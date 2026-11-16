# Bounded scalar semantics

The feature reference is Compact 0.36.1 at `7fa3a117c5e7efe9d2c51da04263e5f0b3509144`. Nightlean uses its observed scalar semantics as a comparison contract. The source syntax, typed representation and backend remain Nightlean's own.

`Nightlean/ScalarPolicy.lean` is an executable policy foundation. It does not add bounded integers to the circuit DSL, native lowering or runtime ABI. Those changes belong to the bounded-integer implementation package. The feature matrix remains unverified.

## Bounds

Normalize unsigned types to an inclusive maximum. A width of `bits` permits values from zero through `2^bits - 1`. An exclusive bound of `limit` permits zero through `limit - 1`, with positive `limit`. The reference accepts widths through 248 and requires every normalized maximum to be at most `2^248 - 1`. Width zero represents the single value zero.

Arithmetic inference uses operand maxima, not the bit lengths or the values supplied at runtime. Addition produces maximum `m + n`, multiplication produces `m * n`, and subtraction preserves the left maximum `m`. Inference rejects a result maximum outside the supported range. Unsigned subtraction rejects a negative result. Native field subtraction wraps modulo the field order.

For two eight-bit unsigned inputs, addition therefore produces maximum 510 and multiplication maximum 65025. Their exclusive bounds are 511 and 65026. The reference prose gives looser bounds of 512 and 65536. The pinned compiler implementation supplies the comparison rule. The [baseline report](../research/compact-equivalence-baseline.md) records the source trace and ten parameter-based conformance cases.

## Conversions and literals

All supported unsigned values embed in the native field without reduction. A narrowing conversion checks the destination range. Conversion to Boolean maps zero to false and every other valid scalar to true. Boolean-to-numeric conversion uses zero or one and still checks the destination range, including a destination permitting only zero.

Boolean arithmetic requires an explicit conversion. A mixed field/unsigned operation produces a field result. Small numeric literals infer an unsigned prefix range ending at the literal value, rather than a singleton refinement type. Larger literals require canonical field values. Nominal aliases, composite values, contextual literal elaboration and subtyping across declarations require separate compiler rules.

## Evidence and remaining implementation

`tests/ScalarPolicy.lean` checks 23 boundary, arithmetic, conversion, literal and invalid-value cases. Lean checks proofs of range preservation for addition, multiplication, subtraction and widening, plus normalization of the exclusive addition bound. The policy also proves the maximum unsigned value is smaller than the native field order.

This establishes a tested semantic policy, not a proof of compiler correctness. The compiler slice still needs typed expressions, elaboration/coercion rules, checked inputs and ledger reads, circuit range constraints, runtime canonical encodings and matching evaluator behavior. Negative circuit tests must reject an altered witness outside a declared bound and subtraction underflow. A finalized ledger round trip must exercise the integer representation before the implementation ticket closes.

The policy has no Compact runtime or compiler dependency. No reference compiler was executed to obtain these results.
