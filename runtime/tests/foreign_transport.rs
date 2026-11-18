#![cfg(feature = "zkir-321")]

use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use num_bigint::BigUint;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn value(ty: &str, bytes: Vec<u8>) -> Json {
    json!({"kind":"foreign","type":ty,"bytes":bytes})
}

fn field_boundary(ty: &str, property: &str) -> Vec<u8> {
    let fixture: Json =
        serde_json::from_str(include_str!("fixtures/foreign-codec/321/encoding.json")).unwrap();
    let row = fixture["fields"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["type"] == ty && row["value"] != "0" && row["value"] != "1")
        .unwrap();
    let mut bytes = BigUint::parse_bytes(row[property].as_str().unwrap().as_bytes(), 10)
        .unwrap()
        .to_bytes_le();
    bytes.resize(32, 0);
    bytes
}

fn inputs_and_results(choose: bool) -> (BTreeMap<String, Json>, BTreeMap<String, Json>) {
    let mut inputs = BTreeMap::from([("choose".into(), json!(choose))]);
    let mut returns = BTreeMap::new();
    for (suffix, source_type, native_type, generator) in [
        (
            "K",
            "Secp256k1",
            "Secp256k1",
            "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
        ),
        (
            "R",
            "Secp256r1",
            "Secp256r1",
            "036b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
        ),
    ] {
        for role in ["Base", "Scalar", "Point"] {
            let source_type = format!("{source_type}{role}");
            let actual = if role == "Point" {
                hex::decode(generator).unwrap()
            } else {
                field_boundary(&format!("{role}<{native_type}>"), "value")
            };
            let mut fallback = vec![0; if role == "Point" { 33 } else { 32 }];
            if role == "Base" {
                fallback[0] = 1;
            }
            let expected = value(&source_type, if choose { actual.clone() } else { fallback });
            inputs.insert(format!("actual{suffix}{role}"), value(&source_type, actual));
            inputs.insert(format!("expected{suffix}{role}"), expected.clone());
            returns.insert(format!("{}{role}", suffix.to_lowercase()), expected);
        }
    }
    (inputs, returns)
}

#[test]
fn typed_foreign_inputs_constants_selection_and_results_match_native() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/foreign-transport/321/ForeignTransport.inspect.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/foreign-transport/321/ForeignTransport.inspect.zkir").as_slice(),
    )
    .unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    for choose in [true, false] {
        let (inputs, expected) = inputs_and_results(choose);
        let mut execution = prepare(
            &plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        assert_eq!(execution.returns_json(), expected);
        assert_eq!(execution.preimage.private_transcript.len(), 19);
        let original = execution.preimage.public_transcript_outputs[0];
        execution.preimage.public_transcript_outputs[0] = original + Fr::from(1u64);
        assert!(check(&execution, &circuit).is_err());
        execution.preimage.public_transcript_outputs[0] = original;
        execution.preimage.private_transcript[8] = Fr::from(2u64);
        assert!(check(&execution, &circuit).is_err());
        let mut malformed = inputs.clone();
        malformed.get_mut("actualKBase").unwrap()["type"] = json!("Secp256r1Base");
        assert!(
            prepare(
                &plan,
                &malformed,
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )
            .is_err()
        );
        let mut alias = inputs.clone();
        alias.get_mut("actualKBase").unwrap()["bytes"] =
            json!(field_boundary("Base<Secp256k1>", "modulus"));
        assert!(
            prepare(
                &plan,
                &alias,
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )
            .is_err()
        );
    }
}
