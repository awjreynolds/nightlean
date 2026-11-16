//! Opt-in source conformance against the actually linked native release.
use nightlean_runtime::{canonical_field, zkir::IrSource};
use serde_json::Value as Json;
use std::{borrow::Cow, fs, path::PathBuf};
use transient_crypto::proofs::{KeyLocation, ProofPreimage};
#[test]
#[ignore = "requires fresh compiler-generated scalar circuits in NIGHTLEAN_SCALAR_SOURCE_DIR"]
fn all_adversarial_scalar_cases_run_on_selected_native_pin() {
    let directory = PathBuf::from(
        std::env::var_os("NIGHTLEAN_SCALAR_SOURCE_DIR").expect("NIGHTLEAN_SCALAR_SOURCE_DIR"),
    );
    let cases: Vec<Json> =
        serde_json::from_slice(include_bytes!("../../tests/scalars/constraint-cases.json"))
            .unwrap();
    let fields = |values: &Json| -> Vec<_> {
        values
            .as_array()
            .unwrap()
            .iter()
            .map(|v| canonical_field(v.as_str().unwrap()).unwrap())
            .collect()
    };
    for case in cases {
        let circuit = IrSource::load(
            fs::File::open(directory.join(format!("{}.zkir", case["circuit"].as_str().unwrap())))
                .unwrap(),
        )
        .unwrap();
        let preimage = ProofPreimage {
            inputs: vec![],
            private_transcript: fields(&case["private"]),
            public_transcript_inputs: fields(&case["publicInputs"]),
            public_transcript_outputs: fields(&case["publicReads"]),
            binding_input: 42u64.into(),
            communications_commitment: None,
            key_location: KeyLocation(Cow::Borrowed("scalar-native-conformance")),
        };
        let result = preimage.check(&circuit);
        assert_eq!(
            result.is_ok(),
            case["accepted"].as_bool().unwrap(),
            "{}",
            case["id"]
        );
        if let Some(expected) = case.get("activityGroups") {
            assert_eq!(
                result.unwrap().len(),
                expected.as_u64().unwrap() as usize,
                "{}",
                case["id"]
            );
        }
    }
}
