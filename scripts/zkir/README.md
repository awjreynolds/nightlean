# ZKIR conformance tools

The compiler remains Lean. These JavaScript tools call exact official release libraries to qualify compiler output.

Run `npm ci --prefix scripts/zkir --ignore-scripts`, then `node scripts/zkir/verify.mjs INPUT.zkir [OUTPUT.bzkir]` for parse, circuit sizing, and binary roundtrip checks. This command does not prove or deploy a contract.

Generate keys with official native `zkir-v3 compile INPUT.zkir KEY.prover KEY.verifier`. `node scripts/zkir/claim-witness.mjs /private/tmp/claim-witness.json` produces public development fixture values for the two-level Lean claim example. This witness file contains private fixture data and belongs outside tracked source.

With the Nightlean localnet proof server on loopback port 16300, run `node scripts/zkir/prove-relation.mjs INPUT.zkir KEY.prover KEY.verifier /private/tmp/claim-witness.json /private/tmp/claim.proof`. Override the loopback URL with `NIGHTLEAN_PROOF_SERVER` if needed. The harness performs official preprocessing checks and sends a native proof request. The server self-verifies before returning success.

The experimental harness serializes explicit standalone relation statement vectors. These are synthetic transcript data, not a ledger's encoded Impact call transcript. A successful proof here does not establish ledger state reads, replay rejection, transaction acceptance, or Preview deployment. See `docs/development/backend-spike.md` for observed results and the remaining binding boundary.
