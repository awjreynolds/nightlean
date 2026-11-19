# Wire codecs in helpers

Use `serialize(value, width)` and `deserialize(Type, frame)` for scalar values in ordinary circuits and readable witness helpers. Both lower through the same Lean codec. The hosted Rust evaluator checks the same boolean and unsigned bounds and the same canonical Native encoding before returning a witness result. [Scalar formats](scalar-serialization.md)

For a typed aggregate, define a Lean `Helpers.Wire.Codec` with the payload type, its declarations and a fixed frame width. Import the codec into a readable circuit with `using`. `decode` expects exactly that frame width. `encode` expects the codec's payload type and returns its declared frame width. A local `let` holds the decoded aggregate.

```lean
noctium_witness_circuit transcode using paymentWire where
  private frame : Bytes 10
  output encoded : Bytes 10 :=
    let payment := decode(paymentWire, frame) in
    disclose(encode(paymentWire, payment))
end
```

The compiler generates one pair of checked helpers per selected codec. Programs composed directly in Lean continue to use `Noctium.Helpers.Wire.declarations` with a checked `Types.CompiledType`. [Complete payment example](../../examples/AggregateSerialization.lean)

The codec walks record fields in declaration order, tuples and vectors in index order, and fixed bytes in byte order. An enum with fieldless variants uses its bounded ordinal. Unit fields occupy zero bytes. Each scalar uses its own encoded width. The encoder pads the end with zeros, and the decoder consumes the typed prefix. Values and derived results retain their privacy origins. Disclose the result explicitly before making it public. [Pinned Compact format](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/analysis-passes/expand-serialize.ss)

## Use decoded values in a proof

A circuit-level `let` binds the record once. `field` selects a record field. `elementAt` selects a zero-based literal index in an aggregate tuple, vector or byte string. `enumTag` reads the variant ordinal as Native. The compiler checks names and fixed indices and retains private origins through each projection.

```lean
noctium_witness_circuit authorize using paymentWire where
  private frame : Bytes 10
  let payment := decode(paymentWire, frame)
  prove elementAt(field(payment, info), 1)
  prove elementAt(field(payment, flags), 1)
  prove eq(enumTag(field(payment, side)), 0)
  output code : UInt 8 := disclose(elementAt(field(payment, memo), 1))
end
```

A successful call establishes the three predicates and returns one memo byte. The other decoded fields stay out of the return value. The fixed-index form uses the checked projection and adds no dynamic selection.

For a fixed vector, `elementAt` also accepts a Native or UInt expression. The `choose` example reads a public vector of three options and uses a private position. `disclose(position)` authorizes the position's influence on the released result. The position stays a private circuit input. When option values are distinguishable, the result still reveals which position was selected. [Complete example](../../examples/AggregateSerialization.lean)

## Focused qualification

The payment example contains a tuple, a fixed vector, a fieldless enum and a two-byte memo. Its input frame ends in `[200, 255]`. Both Noctium and Compact 0.36.1 return `[44, 1, 1, 0, 1, 1, 12, 42, 0, 0]` and reject a wrong UInt, Bool or ordinal in the prefix. The hosted helper and native checker agreed on the Native frame, and the host rejected the modulus encoding.

The readable payment circuit emits the same ZKIR bytes as the prior helper program at `535bc33`. The pinned tool reports 985 rows at K10 after the intervening byte-packing optimization. The authenticated host session and native checker agreed on the payment result and rejected the three malformed frames. Authoring also rejects an incorrect frame width and an output lacking explicit disclosure. [Focused Rust test](../../runtime/tests/aggregate_serialization.rs)

The new approval entrypoint measures K9 and 290 rows. Compact 0.36.1's pure evaluator and Noctium's authenticated host both returned 42 from `[44, 1, 1, 0, 1, 0, 12, 42, 200, 255]` and rejected changes at offsets 2, 4 and 5 to 0, 0 and 1 respectively. The pinned checker accepted the matching statement and rejected the same changes in the private preimage. It also rejected changing 42 to 43 while keeping the committed return. These results qualify the new entrypoint at the source and native checker boundaries. [Compact 0.36.1 release](https://github.com/LFDT-Minokawa/compact/releases/tag/compactc-v0.36.1) · [Focused Rust test](../../runtime/tests/aggregate_serialization.rs)

The vector lookup returns 12, 42 and 88 for positions 0, 1 and 2. The Rust host and native circuit reject 3 and 255. The native checker also rejects replacing the selected position while keeping the original return commitment. The final checked vector element serves as the fallback in the circuit, saving two selectors and one comparison. ZKIR dropped from 107 to 104 instructions and 162 to 158 rows at K9. The three other circuit relations match byte for byte. Raw Impact preparation builds a candidate preimage and the native checker enforces its bounds. [Focused Rust test](../../runtime/tests/aggregate_serialization.rs)

Compact 0.36.1 rejected direct `options[position]` with a runtime index. Its explicit three-case implementation with a bound assertion returned the same three values and rejected the same two invalid positions. This comparison covers behavior with the fixed vector and public frame used above. [Compact sequence reference rules](https://docs.midnight.network/compact/reference/compact-reference#tuple-vector-and-byte-vector-references)

The selected `choose` entrypoint from compiler revision `8002a38` finalized on the pinned Ledger 9.1.0.1 localnet. The Rust client generated the ZKIR 3.2.1 proof, funded both transactions with the development wallet, and verified the exact finalized contract state. The authenticated manifest digest was `114b2a3901d9ef0393103a9f31d128452cd3fd06aeab71906cdb3705a6009f49`.

| Vector lookup action | Finalized block | Transaction ID |
| --- | ---: | --- |
| Deploy | 31598 | `c5cd0bf53321868361ac621ba683756a2aeb27089b077ad768bbbbf7c7b9faed` |
| Call | 31601 | `0cda6c71eb67593d3faf752e4602a932d20e35f2ff06df4a7eaea8aa592d8daf` |

Using direct byte reads for the memo reduced the circuit from 1,025 to 987 rows and brought K from 11 to 10. The native proof finalized on the pinned Ledger 9.1.0.1 and ZKIR 3.2.1 localnet.

| Action | Block | Transaction ID |
| --- | ---: | --- |
| Deploy | 31155 | `3c4a54af494cf956a776d86a932dca9dd13278ff100ce1fc9e2175bda2d5cb66` |
| Call | 31158 | `897f87eb33d07d0627c0534cd6977283307c9027d9ee9600ca72a513a2b515d1` |

The `readPayment` entrypoint returns the decoded record through `return payment`. Noctium's authenticated host and native call reconstruct the same record that the pinned Compact evaluator returns. The selected native relation uses K9 and 298 rows. [Named aggregate returns](committed-returns.md)

Mixed scalar and aggregate circuit outputs, payload-carrying wire enum variants and wider host qualification remain open.

```sh
lake build noctium Noctium.Helpers.Wire
.lake/build/bin/noctium compile examples/AggregateSerialization.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit witness --output build/experiments/aggregate-wire
NOCTIUM_AGGREGATE_WIRE_ARTIFACTS="$PWD/build/experiments/aggregate-wire" \
  cargo test --manifest-path runtime/Cargo.toml --locked --no-default-features \
  --features zkir-321 --test aggregate_serialization -- --ignored
```
