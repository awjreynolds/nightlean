# Bytes32 witness-circuit results

A readable witness circuit may return a logical Bytes32 value. The native
backend binds the result as the existing two canonical Native fields. A contract
uses the full value as a Bytes32 key through the byte-alias path.

`tests/NativeBytes32WitnessOutput.lean` derives an account hash from a private
secret, explicitly discloses the hash and uses the result directly as the actual
ledger key. The private secret stays private. An undisclosed output rejects.

The focused selected-3.2.1 Rust case runs the control Session, obtains native
inputs from private completion and checks the emitted entrypoint relation. The
stored key matches independent SHA-256. Changing only digest byte 31 fails the
helper equality during preparation. This distinguishes full Bytes32 binding
from a 248-bit digest projection. The focused case passes in 0.01 seconds.

The standalone single-result helper relation has two Native output fields.
The source/helper metadata keeps one logical `Bytes<32>` result.

`tests/NativeGroupedBytes32WitnessOutput.lean` returns a record containing an
account ID and a UInt8 count. Its checked aggregate ABI uses 33 physical leaves:
32 range-checked byte projections and the count. The frontend preserves the
logical Bytes32 expression, including lexical `let` bindings, for use as a
ledger key. Physical aggregate leaves cast the checked bytes to Native to match
the existing layout codec. The source expression remains typed as Bytes32.

One focused native case covers both result forms. It checks the source Session,
native relation, full SHA-256 map key and stored count. Changing digest byte 31
rejects during preparation or official native checking. The case passes in
0.02 seconds. This does not establish general nominal ABI equivalence, mobile
bindings or proof generation for grouped results.

Readable witness expressions also accept `toBytes32` for Native, JubjubScalar
and JubjubPoint values through the existing typed serialization routes.
The delegated token workload uses Native serialization for its exact mixed
nonce preimage. No new ZKIR opcode is required. This extends source authoring and
host control, with no new keys, proofs or deployment.
