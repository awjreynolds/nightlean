# Committed getter results

Entrypoints return named Native, Bool, bounded UInt, fixed Bytes, Jubjub and
supported foreign-curve values. Helper entrypoints also return checked composite
values. Return expressions resolve after state effects, including ledger reads after writes.
`tests/NativeReturns.lean` contains a getter and an update operation:

```lean
read balance as currentBalance
read count as currentCount
return balanceValue : Native := currentBalance
return countValue : UInt 64 := currentCount
return enabledValue : Bool := enabled
```

Return declarations must be trailing statements at the entrypoint's top level.
Labels are unique. The type checker validates each expression against the final
read environment. Returning private data requires explicit `disclose(...)`.
This authorizes release to the application result channel. The return itself
does not put clear values in the transaction's ledger call.

Logical returns expand into canonical Native Fields in declaration order:

| Logical type | Native fields |
| --- | --- |
| Native, Bool, UInt | One field; Bool and UInt retain their bounds |
| Bytes32 | Two chunks, using the existing FAB byte-alignment order |
| Bytes(n) | `ceil(n / 31)` chunks in FAB order, including zero fields for Bytes0 |
| JubjubScalar | One canonical scalar-to-Native encoding |
| JubjubPoint | Two affine coordinates, x then y |
| Foreign curve values | The native family's canonical encoded fields |
| Composite helper result | One Native field per checked layout leaf |

Point and scalar values retain the existing canonical/subgroup input and
expression checks. Bytes32 results retain every digest bit. The 256-field output
limit applies after expansion.

The compiler emits those values as ZKIR outputs. The native call prototype's
`output` contains the same fields, and Midnight commits them with the call input
and communication randomness. The ledger stores that commitment. It does not
need a separate clear return field.

## Native call arguments

An entrypoint selects committed arguments from its private inputs:

```lean
entry advance uses returnInput arguments [amount] where
  read balance as beforeBalance
  write balance := disclose(add(beforeBalance, amount))
end
```

The ordered `callInputs` list becomes the native relation's input header and
`ContractCallPrototype.input`. Selected values no longer appear in the private
witness transcript. The communication commitment binds these arguments together
with the returned fields. Selecting an argument preserves its privacy. A
private value or decision reaching a public state write or result still
requires explicit `disclose`.

Direct entrypoints accept Native, Bool, bounded UInt, fixed Bytes, Jubjub
scalars and points, and the supported foreign-curve values. Inputs use the
same field order as the return table above. Bytes use FAB chunks from high to
low, and Bytes0 contributes no fields. Foreign values keep their exact native
type in the input header. UInt and Bool ranges, byte chunk bounds and the
Jubjub canonicality checks still run in the circuit.

The compiler and bundle reader require exact header names, types and order.
Unknown, duplicate or public selections reject. Limits are 256 logical
arguments and 256 physical fields after encoding. Composite arguments and
hosted-witness authoring for committed arguments remain open.
The [typed argument example](../../tests/TypedCallArguments.lean) exercises mixed
input types, an independent private witness and the field order through the
native checker. A reordered header or an out-of-range byte chunk rejects even
with a recomputed commitment.

Rust callers prepare the operation, run `check(&execution, &circuit)`, then read
`execution.returns()` or `execution.returns_json()`. Primitive values retain their
logical types, so JSON uses booleans for Bool and decimal strings for Native and UInt.
Bytes32 uses `{kind:"bytes", values:[...]}`; scalar and point JSON use their
existing `jubjubScalar` and `jubjubPoint` shapes. The C runtime's completed JSON
response adds `result.returns` when nonempty.
Native transaction assembly uses the evaluated output and fresh communication
randomness. Bundle validation checks agreement among the plan return schema,
compiler metadata and native output header.

Composite helper results use `returnViews` metadata. Each view contains a logical
name, canonical schema and ordered physical Native return names. The runtime
validates the schema, field mapping and values during preparation and completion.
`returns()` retains physical fields for native callers. `returns_json()` groups
them into typed record, tuple, vector, enum, bytes and Unit JSON and omits their
physical aliases. The existing C JSON result path exposes the same logical views.
Empty composites retain their logical result with zero physical fields.

Enums retain their variant tag and canonical padding checks. Bool and UInt fields
retain their bounds. Reordered or reused field mappings reject. A private field
still needs explicit disclosure in the source, including fields nested in a
composite result. Views never authorize disclosure. The current limit is 256
physical Native return fields and 256 logical views.

The source metadata includes return labels, types and expressions. Existing
entrypoints omit the optional `returns` field and keep empty native outputs.
The JavaScript development harness rejects nonempty returns instead of treating
them as an empty output. The native Rust runtime implements this feature.

`runtime/tests/native_returns.rs` provides one focused native sequence: getter,
two updates, and getter again, with exact expected balances, counters and Bool
results. It compares the output commitment and rejects a forged commitment,
a forged return expression and a mismatched declared return type. The source
fixture rejects a private return without disclosure.
The update operation now uses `amount` as a native call argument. The case checks
its raw preimage slot and absence from the private transcript. Changing that
argument still rejects after recomputing its communication commitment, because
the existing state transition and outputs no longer match.

`tests/NativeOpaqueReturns.lean` and `runtime/tests/native_opaque_returns.rs`
add one source/native example for Bytes32 and Jubjub results. Independent SHA-256
and group arithmetic agree with the named results and their six-field commitment.
The case covers a full-range scalar and rejects an altered digest high byte.

`tests/NativeBytes.lean`, `tests/ForeignOperations.lean` and `tests/Curve25519.lean`
also supply retained source/native return cases for general bytes and foreign
families. The staged helper path in `tests/IterationWitness.lean` returns a receipt
with a total, Bool vector, enum claim, bytes, nested Unit and an explicitly released
private offset. Its eight Native fields form one committed SDK result. The native
case checks active and inactive records and rejects an altered provider response.
Source guards reject removal of the field's disclosure. Codec checks reject
noncanonical Bool/UInt leaves and retain empty values.

This is scoped native-checker evidence. No new keys, proofs or deployments were
generated. Readable composite return syntax and generated language bindings remain separate
work. See the [native call protocol](native-call-claims.md) for composition evidence.
