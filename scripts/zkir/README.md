# ZKIR conformance tools

The compiler remains Lean. These JavaScript tools call exact official release libraries to qualify compiler output.

Run `npm ci --prefix scripts/zkir --ignore-scripts`, then `node scripts/zkir/verify.mjs INPUT.zkir [OUTPUT.bzkir]` for parse, circuit sizing, and binary roundtrip checks. This command does not prove or deploy a contract.

Build the pinned independent CLI with `node scripts/zkir/bootstrap-native.mjs /private/tmp/nightlean-native-zkir`, then generate keys with `/private/tmp/nightlean-native-zkir/bin/zkir compile INPUT.zkir KEY.prover KEY.verifier`. Rust 1.100.0 and a native C toolchain are required. See [toolchain provenance](../../docs/development/native-toolchain.md).

For the complete source-driven native deployment and claim, follow [the native workflow](../../docs/development/native-contract.md). It consumes the CLI's emitted `.impact.json` runtime plan and actual ledger parameters.

`node scripts/zkir/claim-witness.mjs /private/tmp/claim-witness.json` separately produces development values for the standalone relation example. This witness file belongs outside tracked source.

With the Noctium localnet proof server on loopback port 16300, run `node scripts/zkir/prove-relation.mjs INPUT.zkir KEY.prover KEY.verifier /private/tmp/claim-witness.json /private/tmp/claim.proof`. Override the loopback URL with `NIGHTLEAN_PROOF_SERVER` if needed. The harness performs official preprocessing checks and sends a native proof request. The server self-verifies before returning success.

The experimental harness serializes explicit standalone relation statement vectors. These are synthetic transcript data, not a ledger's encoded Impact call transcript. A successful proof here does not establish ledger state reads, replay rejection, transaction acceptance, or Preview deployment. See `docs/development/backend-spike.md` for observed results and the remaining binding boundary.
