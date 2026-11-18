//! Real native verification, separate from evaluator/preprocessing checks.
use noctium_runtime::canonical_field;
use serialize::tagged_deserialize;
use sha2::{Digest, Sha256};
use std::{fs, path::PathBuf};
use transient_crypto::proofs::{ParamsVerifier, Proof, VerifierKey};

#[test]
#[ignore = "requires source-generated disclosure keys, native proof and pinned k5 parameters"]
fn authorized_release_proof_binds_every_public_field() {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_DISCLOSURE_FIXTURE")
            .expect("set NOCTIUM_DISCLOSURE_FIXTURE to the qualified material directory"),
    );
    let key_bytes = fs::read(directory.join("authorizedRelease.verifier")).unwrap();
    let mut key_reader = key_bytes.as_slice();
    let key: VerifierKey = tagged_deserialize(&mut key_reader).unwrap();
    assert!(key_reader.is_empty());
    let proof_bytes = fs::read(directory.join("authorizedRelease.proof")).unwrap();
    let mut proof_reader = proof_bytes.as_slice();
    let versioned: ledger::structure::ProofVersioned =
        tagged_deserialize(&mut proof_reader).unwrap();
    assert!(proof_reader.is_empty());
    let proof = match versioned {
        ledger::structure::ProofVersioned::V2(proof) => proof,
        _ => panic!("expected the qualified native v2 proof representation"),
    };
    let parameter_bytes = fs::read(directory.join("bls_midnight_2p5")).unwrap();
    assert_eq!(
        hex::encode(Sha256::digest(&parameter_bytes)),
        "0a1c9229f315fc1868ff25f668fb83aec4d09f4f23a706b5197c692c619d72c6"
    );
    let parameters = ParamsVerifier::read(parameter_bytes.as_slice()).unwrap();
    // Binding input, public parameter Impact, explicitly released output Impact.
    let statement = vec![canonical_field("42").unwrap(); 3];
    key.verify(&parameters, &proof, statement.iter().copied())
        .unwrap();
    for index in 0..statement.len() {
        let mut changed = statement.clone();
        changed[index] = canonical_field("43").unwrap();
        assert!(
            key.verify(&parameters, &proof, changed.into_iter())
                .is_err()
        );
    }
    let mut damaged = Proof(proof.0.clone());
    *damaged.0.last_mut().unwrap() ^= 1;
    assert!(
        key.verify(&parameters, &damaged, statement.into_iter())
            .is_err()
    );
}
