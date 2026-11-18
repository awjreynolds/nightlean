# Typed Boolean gates

`boolAnd(left, right)`, `boolOr(left, right)` and `boolXor(left, right)` take two `Bool` expressions. They evaluate both operands. Use the existing short-circuit witness controls when the right operand should run conditionally.

```lean
import Noctium.Frontend
open scoped Noctium

noctium_circuit eligible where
  private member : Bool
  private unused : Bool
  output allowed : Bool := disclose(boolAnd(member, unused))
end
```

The public and private source ABI still represents Boolean values as constrained Native fields, zero or one. Each new gate bridges its operands to the native `Bool` type using typed `load_constant` values and `cond_select`, emits `and`, `or` or `xor`, then encodes the result back to one Native field. Existing Boolean source paths retain their representation.

Private origins propagate through each gate. Releasing a result requires `disclose`. Both operand computations retain their assertions, including the right operand of `boolAnd(false, ...)` and `boolOr(true, ...)`. These gates do not authorize disclosure or hide information in a public result.

The producer validates actual typed Bool operands, nonempty native gate inputs and canonical single-field Bool constants. A constrained Native field is insufficient as a typed gate operand until bridged. Other `load_constant` codecs remain unsupported.

The focused source and native cases are [BooleanGates.lean](../../tests/BooleanGates.lean) and [native_boolean_gates.rs](../../runtime/tests/native_boolean_gates.rs). They cover truth tables, nested XOR parity, output binding, eager assertions and malformed producer operands. A host Session case exercises the witness interpreter. This slice adds no keys, proofs or deployment qualification.

The separate formal witness semantics needs reconciliation with the expanded byte, curve and Boolean language. [Issue 21](https://github.com/awjreynolds/noctium/issues/21#issuecomment-6971590829) tracks that gap. The focused execution cases do not establish witness-erasure or whole-language preservation.
