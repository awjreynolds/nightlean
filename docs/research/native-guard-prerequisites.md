# Native guarded ZKIR prerequisites

Status checked 2026-11-17. This note records a raw ZKIR 3.2.1 experiment for Noctium issue 43. The feature gate stays closed. Native ZKIR acceptance does not mean Noctium supports input guards, conditional Impact, skipped public groups, or guarded source branches.

The experiment used the pinned [ZKIR source](https://github.com/midnightntwrk/midnight-zkir/tree/7a51b3385bbf4bce3604df87a7c70867c9ab43c0), the release checker package, the native keygen CLI, and K4/K5 parameter files already present in the local verified cache. It added no application dependency. Node is used only by this optional development protocol probe. The broader coverage and safety requirements remain in [full ZKIR coverage](zkir-v3-full-coverage.md) and [3.2.1 qualification](../development/zkir-3.2.1-qualification.md).

## Reproduce

First obtain the pinned CLI, checker package, and verified parameter files through the existing native setup documented in [3.2.1 qualification](../development/zkir-3.2.1-qualification.md). The CLI reports `midnight-zkir 3.2.0` because the tagged crate version was not bumped. The source revision and executable hash below distinguish this 3.2.1 build.

Set explicit paths, then compile the three checked-in JSON fixtures. `zkir compile` writes each `.bzkir` tagged binary IR beside its `.zkir` JSON input.

```sh
ZKIR=/path/to/pinned-zkir-3.2.1/bin/zkir
CHECKER=/path/to/zkir-v3-3.2.1/package/midnight_zkir_wasm_fs.js
CHECKER_WASM=/path/to/zkir-v3-3.2.1/package/midnight_zkir_wasm_bg.wasm
PARAMS=/path/to/verified-midnight-parameters
ARTIFACTS="$(mktemp -d /tmp/noctium-guarded-native.XXXXXX)"

cp tests/guarded-native-prerequisites/*.zkir "$ARTIFACTS/"
for circuit in guarded-impact input-guards private-input-guard; do
  MIDNIGHT_PP="$PARAMS" "$ZKIR" compile \
    "$ARTIFACTS/$circuit.zkir" \
    "$ARTIFACTS/$circuit.prover" \
    "$ARTIFACTS/$circuit.verifier"
done

node tests/guarded-native-prerequisites/probe.mjs \
  --checker "$CHECKER" --wasm "$CHECKER_WASM" --cli "$ZKIR" \
  --params "$PARAMS" --artifacts "$ARTIFACTS" --mode check
```

Checker mode is the default. It validates the CLI, checker package manifest, checker JS/WASM, K4/K5 parameters, fixtures, and tagged binary IR hashes before importing the checker. It performs no network request and does not import the ledger package. The result prints exact JSON, binary IR, prover-key, and verifier-key hashes.

Optional proof mode needs the already-running official proof server. It never starts or restarts a service. Verify the service image as `midnightntwrk/proof-server@sha256:5617e26aa76d06c44f4bee667c37eb71ccf02fefe0e5848100fa84001282d515`, then pass its explicit loopback origin:

```sh
node tests/guarded-native-prerequisites/probe.mjs \
  --checker "$CHECKER" --wasm "$CHECKER_WASM" --cli "$ZKIR" \
  --params "$PARAMS" --artifacts "$ARTIFACTS" --mode prove \
  --proof-url http://127.0.0.1:16300
```

The probe accepts only HTTP(S) loopback origins without credentials, paths, queries, or fragments. It omits credentials, rejects redirects, limits requests and responses to 1 MiB (error responses to 4 KiB), and applies a 120 second timeout. The pinned ledger prover verifies each generated proof against its verifier key before returning success ([source](https://github.com/midnightntwrk/midnight-ledger/blob/a2b30128ca4b660b73a068e29b56b48ede8c9a74/transient-crypto/src/proofs.rs#L752)). The probe reports the returned proof bytes and hash. Verify the proof-server image separately because an arbitrary loopback service does not establish that implementation boundary.

## Native behavior observed

The fixtures use the native JSON schema directly. `Impact` accepts a runtime `Native` Boolean guard and a vector of `Native` operands ([instruction definition](https://github.com/midnightntwrk/midnight-zkir/blob/7a51b3385bbf4bce3604df87a7c70867c9ab43c0/zkir/src/ir.rs#L510)). In preprocessing, the public-input vector begins with the binding input. Each inactive Impact appends one zero per operand and one `Some(operand_count)` activity entry. Each active Impact appends its values in instruction order, checks them against the corresponding public transcript fields, and appends `None` ([preprocessing](https://github.com/midnightntwrk/midnight-zkir/blob/7a51b3385bbf4bce3604df87a7c70867c9ab43c0/zkir/src/ir_vm.rs#L588)). In-circuit, the guard becomes an assigned bit and each operand is selected against zero ([synthesis](https://github.com/midnightntwrk/midnight-zkir/blob/7a51b3385bbf4bce3604df87a7c70867c9ab43c0/zkir/src/ir_vm.rs#L1111)).

The two successful two-group cases produced these source-determined vectors and checker activity results. Communications commitment is disabled in these fixtures, so the binding input is followed directly by the Impact fields.

| Case | Impact operands | Public transcript fields | Public vector | `pi_skips` | Checker result |
| --- | --- | --- | --- | --- | --- |
| Group 0 off, group 1 on | Group 0 has 2, group 1 has 1 | `[255]` | `[42, 0, 0, 255]` | `[Some(2), None]` | `[2, undefined]` |
| Group 0 on, group 1 off | Group 0 has 2, group 1 has 1 | `[127, 1]` | `[42, 127, 1, 0]` | `[None, Some(1)]` | `[undefined, 1]` |

The checker returns one activity entry per Impact instruction, in instruction order. Its JS API maps active `None` to `undefined` and skipped `Some(n)` to a BigInt count. Inactive group fields do not appear in `public_transcript_inputs`; an inactive field, wrong active value, or unused transcript field caused checker rejection.

`PublicInput` guards read `public_transcript_outputs`; `PrivateInput` guards read `private_transcript`. A false guard supplies the typed default during preprocessing. The guard is ignored during circuit synthesis, so it does not skip later assertions or constraints ([input definitions](https://github.com/midnightntwrk/midnight-zkir/blob/7a51b3385bbf4bce3604df87a7c70867c9ab43c0/zkir/src/ir.rs#L931), [preprocessing](https://github.com/midnightntwrk/midnight-zkir/blob/7a51b3385bbf4bce3604df87a7c70867c9ab43c0/zkir/src/ir_vm.rs#L423), [synthesis](https://github.com/midnightntwrk/midnight-zkir/blob/7a51b3385bbf4bce3604df87a7c70867c9ab43c0/zkir/src/ir_vm.rs#L1241)). In the fixture, a false input guard produced zero and the downstream assertion failed. A true public and private guard consumed the matching transcript values and passed.

The raw fixture expresses inactive constraints explicitly. It selects `predicate` when active and `1` when inactive, then asserts the selected value. It selects the scalar when active and `0` when inactive, then applies `ConstrainBits(8)`. A false guard with predicate `0` and scalar `300` passed; an active scalar `256` failed. `ConstrainToBoolean` rejects guard `2`; the checker and proof service both rejected it. These are raw IR patterns, not source-language lowering or lazy branch semantics.

## Recorded results and hashes

The original native run compiled `guarded-impact` at k=5, 24 rows; `input-guards` at k=4, 7 rows; and `private-input-guard` at k=4, 5 rows. Its official checker run had 4 positive and 10 negative cases. The pinned proof server returned three 3,468-byte proofs and rejected four invalid proving requests with HTTP 400. This was standalone proof generation, not a ledger transaction.

The final original experiment log SHA-256 is `b37f86e4f6dd10b542bd8bbdabba6a4c564ffda7b7c662be4ad924e6c368f4c2`; its probe script SHA-256 is `a7f78294551d546dd657264e583c97a740ce09cd608ba58f23cf9a3a906d5606`. The adapted repository probe was separately rerun in checker-only mode after paths and pins were made explicit. It again reported 4 accepted and 10 rejected cases, with proof service status `not-run`.

| Fixture | `.zkir` JSON SHA-256 | `.bzkir` tagged binary IR SHA-256 | `.prover` key SHA-256 | `.verifier` key SHA-256 |
| --- | --- | --- | --- | --- |
| `guarded-impact` | `e9497768dd02f324212860b3abe8312b2c013615ebc0c719dff15d26b8f7a7ff` | `4391aa308022aaa601d2d813d222a12a009ed2deeaac5b51615bfc580429cabb` | `ae067815237b0c150a412e02c9413fed45e43b44c5ebc5037d90e9179bd65bbf` | `036b48515f5d04a84787ff1cab4de70b8d840d47ca0d5458970d38b955bae15a` |
| `input-guards` | `7b96d32e617c4d87f026906c4c6125011885b8027b351092f5cfc81c546698c8` | `240a23e1344fa9cbb7a2e805e998d423dc00fd33c8f087411fbb11d072dea499` | `254f2aab04b4a2a8bca06115df665c6278799028d34797cd972d5558126308c8` | `7e616de08eef5736792914fe6f80fe200a5cedd21377f90565dec6146b771194` |
| `private-input-guard` | `07a43fd0b339c57ecf28a61c49e81035997261e6829a007aa43dae1ab8bc21cd` | `4f6c26f1121559ed5a351709a9ace111c2a32d2fbaf1407fd93b998c95a863a3` | `83d431c6a7792f0746da077f51473f4bb10a1dcf31cd4b5d5cb88056ad24d21b` | `fb24be692740ce04192ec32d52045376d0e3a4b1b60dd3df46a02449513bcb30` |

The primary guarded Impact proofs had SHA-256 `8b7fc7aae02390461db9b303e6571d47b2742e9a961014eec3ba6aea80b390ec` and `1e915268813d66178ab161e71308402c939878e635fe0612b349baa18687f1a0`. The private-input guard proof had SHA-256 `ed9f92ecb4f941af1d76bcf5572107dd3d62eba1504d4192186b91e23a04d2aa`.

| Pinned file | SHA-256 |
| --- | --- |
| Native CLI, source revision `7a51b3385bbf4bce3604df87a7c70867c9ab43c0` | `7396c9a368e70fb66cb91f39d1508c9f983cacc8d3bc27f7a94e12d9fe327c40` |
| Checker package manifest, `@midnightntwrk/zkir-v3` 3.2.1 | `8fdbb3861ee27d2691d9c50ae50837061657fd5430506f6d7eec19b0910d4a84` |
| Checker module JS | `a4ec641776c45bd06fe033f25b8d74fccca7900d5e97cc360468ddeacfa2424c` |
| Checker WASM | `3568fafaf225469dbbd038b0236d1b6b76e0da19da565caba33efe2ceb682cfc` |
| Existing K4 parameters `bls_midnight_2p4` | `232f401fad10c7ddf8828d2aa4c85c6506c5da09795998cecaeb9f75fc8f6ada` |
| Existing K5 parameters `bls_midnight_2p5` | `0a1c9229f315fc1868ff25f668fb83aec4d09f4f23a706b5197c692c619d72c6` |

The repository additions are limited to public fixtures, an optional probe, and this note. They include no keys, parameters, executables, service credentials, or proof output. This experiment does not claim source-feature enablement, native ledger acceptance, a general privacy property, or a compiler theorem. Keep Noctium issue 43 open and gated until source disclosure analysis, producer validation, and exact native ledger activity correspondence have their own acceptance evidence.
