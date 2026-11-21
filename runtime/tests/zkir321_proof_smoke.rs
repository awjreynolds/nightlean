#![cfg(feature = "zkir-321")]

//! Opt-in native proof regression for a type introduced by an intermediate ZKIR op.
//! The proof and fresh key material stay in memory.
use futures::executor::block_on;
use noctium_runtime::{profile, proof::TrustedParameters, zkir::IrSource};
use rand::rngs::OsRng;
use sha2::{Digest, Sha256};
use std::{borrow::Cow, env, fs};
use transient_crypto::{
    curve::Fr,
    proofs::{KeyLocation, ParamsVerifier, ProofPreimage, Zkir},
};

const CIRCUIT: &[u8] = include_bytes!("../../tests/zkir321/jubjub-intermediate.zkir");
const K: u8 = 10;
const K10_SRS_SHA256: &str =
    "46b2290933cbed4c378889e4ba971f1a92888331ffb09466acd4ff61a1e2cb42";

#[test]
#[ignore = "requires the official k10 SRS in NOCTIUM_ZKIR321_K10_SRS"]
fn zkir_321_jubjub_intermediate_generates_and_binds_a_native_proof() {
    let parameter_path = env::var_os("NOCTIUM_ZKIR321_K10_SRS")
        .expect("set NOCTIUM_ZKIR321_K10_SRS to the pinned official k10 SRS");
    let parameter_bytes = fs::read(parameter_path).expect("official k10 SRS is readable");
    let parameters =
        TrustedParameters::from_bytes(&parameter_bytes, K, K10_SRS_SHA256)
            .expect("official SRS digest and encoding are valid");
    let verifier_parameters = ParamsVerifier::read(parameter_bytes.as_slice())
        .expect("validated SRS loads for native verification");

    let circuit = IrSource::load(CIRCUIT).expect("pinned Jubjub intermediate relation parses");
    assert_eq!(circuit.k(), K);
    let (prover_key, verifier_key) = block_on(circuit.keygen(&parameters))
        .expect("fresh native proving and verification keys generate");

    let binding = Fr::from(42u64);
    let preimage = ProofPreimage {
        inputs: vec![Fr::from(7u64)],
        private_transcript: vec![],
        public_transcript_inputs: vec![],
        public_transcript_outputs: vec![],
        binding_input: binding,
        communications_commitment: None,
        key_location: KeyLocation(Cow::Borrowed("zkir321-jubjub-intermediate")),
    };
    let (proof, statement, activity) =
        block_on(circuit.prove(OsRng, &parameters, prover_key, &preimage))
            .expect("fresh native proof is generated");
    assert!(activity.is_empty());
    assert_eq!(statement, vec![binding]);
    verifier_key
        .verify(&verifier_parameters, &proof, statement.iter().copied())
        .expect("proof verifies for the expected public binding");

    let changed_statement = [Fr::from(43u64)];
    assert!(verifier_key
        .verify(&verifier_parameters, &proof, changed_statement.into_iter())
        .is_err());

    println!(
        "ZKIR proof smoke passed: profile={}, ledger_revision={}, zkir_revision={}, circuit_sha256={}, k={}, srs_sha256={}, keygen=fresh, proof_bytes={}, expected_binding=accepted, changed_binding=rejected",
        profile::NAME,
        noctium_runtime::LEDGER_REVISION,
        profile::REVISION,
        hex::encode(Sha256::digest(CIRCUIT)),
        K,
        parameters.sha256(),
        proof.0.len(),
    );
}
