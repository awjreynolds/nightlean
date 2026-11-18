# Committed getter results

Entrypoints now return named Native, Bool and bounded UInt values. Return
expressions resolve after state effects, including ledger reads after writes.
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

Each scalar return uses one canonical Native Field in declaration order. Bool
values are constrained to 0/1, and UInt values retain their declared bounds.
The compiler emits those values as ZKIR outputs. The native call prototype's
`output` contains the same fields, and Midnight commits them with the call input
and communication randomness. The ledger stores that commitment. It does not
need a separate clear return field.

Rust callers prepare the operation, run `check(&execution, &circuit)`, then read
`execution.returns()` or `execution.returns_json()`. Values retain their logical
types, so JSON uses booleans for Bool and decimal strings for Native and UInt.
The C runtime's completed JSON response adds `result.returns` when nonempty.
Native transaction assembly uses the evaluated output and fresh communication
randomness. Bundle validation checks agreement among the plan return schema,
compiler metadata and native output header.

The source metadata includes return labels, types and expressions. Existing
entrypoints omit the optional `returns` field and keep empty native outputs.
The JavaScript development harness rejects nonempty returns instead of treating
them as an empty output. The native Rust runtime implements this feature.

`runtime/tests/native_returns.rs` provides one focused native sequence: getter,
two updates, and getter again, with exact expected balances, counters and Bool
results. It compares the output commitment and rejects a forged commitment,
a forged return expression and a mismatched declared return type. The source
fixture rejects a private return without disclosure.

This is native-checker evidence for scalar SDK results. No new keys, proofs or
deployments were generated. Composite/byte/curve return layouts, generated
language bindings and the cross-contract claim protocol remain separate work.
