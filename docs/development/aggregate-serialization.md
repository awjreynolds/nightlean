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

The compiler generates one pair of checked helpers per selected codec. Programs composed directly in Lean continue to use `Noctium.Helpers.Wire.declarations` with a checked `Types.CompiledType`. The readable example uses a local aggregate and a single byte-string output. General aggregate projections and named aggregate outputs remain open. [Complete payment example](../../examples/AggregateSerialization.lean)

The codec walks record fields in declaration order, tuples and vectors in index order, and fixed bytes in byte order. An enum with fieldless variants uses its bounded ordinal. Unit fields occupy zero bytes. Each scalar uses its own encoded width. The encoder pads the end with zeros, and the decoder consumes the typed prefix. Values and derived results retain their privacy origins. Disclose the result explicitly before making it public. [Pinned Compact format](https://github.com/LFDT-Minokawa/compact/blob/7fa3a117c5e7efe9d2c51da04263e5f0b3509144/compiler/analysis-passes/expand-serialize.ss)

## Focused qualification

The payment example contains a tuple, a fixed vector, a fieldless enum and a two-byte memo. Its input frame ends in `[200, 255]`. Both Noctium and Compact 0.36.1 return `[44, 1, 1, 0, 1, 1, 12, 42, 0, 0]` and reject a wrong UInt, Bool or ordinal in the prefix. The hosted helper and native checker agreed on the Native frame, and the host rejected the modulus encoding.

The readable payment circuit emits the same ZKIR bytes as the prior helper program at `535bc33`. The pinned tool reports 985 rows at K10 after the intervening byte-packing optimization. The authenticated host session and native checker agreed on the payment result and rejected the three malformed frames. Authoring also rejects an incorrect frame width and an output lacking explicit disclosure. [Focused Rust test](../../runtime/tests/aggregate_serialization.rs)

Using direct byte reads for the memo reduced the circuit from 1,025 to 987 rows and brought K from 11 to 10. The native proof finalized on the pinned Ledger 9.1.0.1 and ZKIR 3.2.1 localnet.

| Action | Block | Transaction ID |
| --- | ---: | --- |
| Deploy | 31155 | `3c4a54af494cf956a776d86a932dca9dd13278ff100ce1fc9e2175bda2d5cb66` |
| Call | 31158 | `897f87eb33d07d0627c0534cd6977283307c9027d9ee9600ca72a513a2b515d1` |

The typed helper API covers these layouts. Readable generic aggregate syntax, payload-carrying variants and broader host qualification remain open.

```sh
lake build noctium Noctium.Helpers.Wire
.lake/build/bin/noctium compile examples/AggregateSerialization.lean \
  --target profiles/midnight-ledger-9-zkir-3.2.1-target.json \
  --emit ledger --emit witness --output build/experiments/aggregate-wire
NOCTIUM_AGGREGATE_WIRE_ARTIFACTS="$PWD/build/experiments/aggregate-wire" \
  cargo test --manifest-path runtime/Cargo.toml --locked --no-default-features \
  --features zkir-321 --test aggregate_serialization -- --ignored
```
