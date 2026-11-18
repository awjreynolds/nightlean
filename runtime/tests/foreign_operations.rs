#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Plan, Value, check, create_state,
    foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignUnaryOp, ForeignValue},
    prepare,
    zkir::IrSource,
};
use num_bigint::BigUint;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn bytes32(number: &BigUint) -> Vec<u8> {
    let mut bytes = number.to_bytes_le();
    assert!(bytes.len() <= 32);
    bytes.resize(32, 0);
    bytes
}

fn field(ty: ForeignType, number: &BigUint) -> Json {
    Value::Foreign(ForeignValue::from_bytes(ty, &bytes32(number)).unwrap()).public_json()
}

fn modulus(name: &str) -> BigUint {
    let fixture: Json =
        serde_json::from_str(include_str!("fixtures/foreign-codec/321/encoding.json")).unwrap();
    let row = fixture["fields"]
        .as_array()
        .unwrap()
        .iter()
        .find(|row| row["type"] == name)
        .unwrap();
    BigUint::parse_bytes(row["modulus"].as_str().unwrap().as_bytes(), 10).unwrap()
}

#[test]
fn source_foreign_operations_match_native_and_preserve_partial_failures() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/foreign-operations/321/ForeignOperations.inspect.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/foreign-operations/321/ForeignOperations.inspect.zkir").as_slice(),
    )
    .unwrap();
    let initial = create_state(
        &plan,
        &[
            "inverseMarker",
            "identityXMarker",
            "coordinatesMarker",
            "decodeMarker",
        ]
        .into_iter()
        .map(|name| (name.into(), json!("0")))
        .collect(),
    )
    .unwrap();
    let raw: Vec<u8> = (0..64).collect();
    let mut inputs = BTreeMap::from([
        ("raw".into(), json!({"kind":"bytes","values":raw})),
        ("enabled".into(), json!(true)),
        ("guardInv".into(), json!(false)),
        ("guardIdentityX".into(), json!(false)),
        ("guardCoordinates".into(), json!(false)),
        ("guardDecode".into(), json!(false)),
    ]);
    let mut expected = BTreeMap::new();
    for (prefix, family, family_name, base, scalar, generator) in [
        (
            "k",
            ForeignFamily::Secp256k1,
            "Secp256k1",
            5u64,
            3u64,
            "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
        ),
        (
            "r",
            ForeignFamily::Secp256r1,
            "Secp256r1",
            7u64,
            5u64,
            "036b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
        ),
    ] {
        let base_type = ForeignType::new(family, ForeignRole::Base);
        let scalar_type = ForeignType::new(family, ForeignRole::Scalar);
        let point_type = ForeignType::new(family, ForeignRole::Point);
        inputs.insert(format!("{prefix}Base"), field(base_type, &base.into()));
        inputs.insert(
            format!("{prefix}Scalar"),
            field(scalar_type, &scalar.into()),
        );
        inputs.insert(
            format!("{prefix}Point"),
            Value::Foreign(
                ForeignValue::from_bytes(point_type, &hex::decode(generator).unwrap()).unwrap(),
            )
            .public_json(),
        );
        let p = modulus(&format!("Base<{family_name}>"));
        let q = modulus(&format!("Scalar<{family_name}>"));
        let inverse = BigUint::from(base).modpow(&(&p - 2u8), &p);
        let base_result = (BigUint::from(base + 2) * inverse) % &p;
        let scalar_result = BigUint::from(2 * scalar + 1) % &q;
        expected.insert(
            format!("{prefix}BaseResult"),
            field(base_type, &base_result),
        );
        expected.insert(
            format!("{prefix}ScalarResult"),
            field(scalar_type, &scalar_result),
        );
        let doubled = ForeignValue::from_bytes(scalar_type, &bytes32(&BigUint::from(2 * scalar)))
            .unwrap()
            .unary(ForeignUnaryOp::MulGenerator)
            .unwrap();
        expected.insert(
            format!("{prefix}PointBytes"),
            json!({"kind":"bytes","values":doubled.to_bytes().unwrap()}),
        );
        expected.insert(
            format!("{prefix}PointResult"),
            Value::Foreign(doubled).public_json(),
        );
    }
    let raw_number = BigUint::from_bytes_le(&raw);
    expected.insert(
        "rawKBase".into(),
        field(
            ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Base),
            &(&raw_number % modulus("Base<Secp256k1>")),
        ),
    );
    expected.insert(
        "rawRScalar".into(),
        field(
            ForeignType::new(ForeignFamily::Secp256r1, ForeignRole::Scalar),
            &(&raw_number % modulus("Scalar<Secp256r1>")),
        ),
    );
    expected.insert(
        "emptyKBase".into(),
        field(
            ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Base),
            &0u8.into(),
        ),
    );
    let execute = |inputs: &BTreeMap<String, Json>| {
        prepare(
            &plan,
            inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
    };
    let mut execution = execute(&inputs).unwrap();
    check(&execution, &circuit).unwrap();
    assert_eq!(execution.returns_json(), expected);
    assert_eq!(execution.after.state.get_ref(), initial.get_ref());
    assert_eq!(execution.preimage.private_transcript.len(), 87);
    execution.preimage.private_transcript[82] = Fr::from(0u64);
    assert!(check(&execution, &circuit).is_err());
    execution.preimage.private_transcript[82] = Fr::from(1u64);
    for (index, flag) in [
        "guardInv",
        "guardIdentityX",
        "guardCoordinates",
        "guardDecode",
    ]
    .into_iter()
    .enumerate()
    {
        execution.preimage.private_transcript[83 + index] = Fr::from(1u64);
        assert!(check(&execution, &circuit).is_err(), "native {flag}");
        execution.preimage.private_transcript[83 + index] = Fr::from(0u64);
        let mut rejected = inputs.clone();
        rejected.insert(flag.into(), json!(true));
        assert!(execute(&rejected).is_err(), "host {flag}");
    }
}
