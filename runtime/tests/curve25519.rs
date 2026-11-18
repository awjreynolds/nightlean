#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Plan, Value, check,
    constructor::construct_state,
    foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignUnaryOp, ForeignValue},
    prepare,
    zkir::IrSource,
};
use num_bigint::BigUint;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn scalar_bytes(number: &BigUint) -> Vec<u8> {
    let mut bytes = number.to_bytes_le();
    assert!(bytes.len() <= 32);
    bytes.resize(32, 0);
    bytes
}

fn foreign(role: ForeignRole, bytes: &[u8]) -> ForeignValue {
    ForeignValue::from_bytes(ForeignType::new(ForeignFamily::Curve25519, role), bytes).unwrap()
}

fn field(role: ForeignRole, number: &BigUint) -> Json {
    Value::Foreign(foreign(role, &scalar_bytes(number))).public_json()
}

#[test]
fn curve25519_source_operations_storage_and_guard_match_native() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/curve25519/321/Curve25519.inspect.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/curve25519/321/Curve25519.inspect.zkir").as_slice(),
    )
    .unwrap();
    let initial = construct_state(&plan, &BTreeMap::new()).unwrap();
    let mut generator_bytes = [0x66; 32];
    generator_bytes[0] = 0x58;
    let generator = foreign(ForeignRole::Point, &generator_bytes);
    let raw: Vec<u8> = (0..64).collect();
    let mut supplied = BTreeMap::from([
        ("base".into(), field(ForeignRole::Base, &5u8.into())),
        ("scalar".into(), field(ForeignRole::Scalar, &3u8.into())),
        (
            "point".into(),
            Value::Foreign(generator.clone()).public_json(),
        ),
        ("rawBytes".into(), json!({"kind":"bytes","values":raw})),
        ("decodeGuard".into(), json!(false)),
    ]);
    let p = (BigUint::from(1u8) << 255usize) - BigUint::from(19u8);
    let q = (BigUint::from(1u8) << 252usize)
        + BigUint::parse_bytes(b"27742317777372353535851937790883648493", 10).unwrap();
    let inverse = BigUint::from(5u8).modpow(&(&p - BigUint::from(2u8)), &p);
    let point_result = foreign(ForeignRole::Scalar, &scalar_bytes(&6u8.into()))
        .unary(ForeignUnaryOp::MulGenerator)
        .unwrap();
    let identity = Value::Foreign(
        ForeignValue::zero(ForeignType::new(
            ForeignFamily::Curve25519,
            ForeignRole::Point,
        ))
        .unwrap(),
    )
    .public_json();
    let identity_bytes = identity["bytes"].clone();
    let expected = BTreeMap::from([
        (
            "baseResult".into(),
            field(ForeignRole::Base, &((inverse * 7u8) % &p)),
        ),
        (
            "scalarResult".into(),
            field(ForeignRole::Scalar, &7u8.into()),
        ),
        (
            "pointResult".into(),
            Value::Foreign(point_result.clone()).public_json(),
        ),
        (
            "pointBytes".into(),
            json!({"kind":"bytes","values":point_result.to_bytes().unwrap()}),
        ),
        (
            "baseBytes".into(),
            json!({"kind":"bytes","values":scalar_bytes(&5u8.into())}),
        ),
        (
            "roundtripPoint".into(),
            Value::Foreign(generator).public_json(),
        ),
        ("identityX".into(), field(ForeignRole::Base, &0u8.into())),
        ("identityY".into(), field(ForeignRole::Base, &1u8.into())),
        (
            "rawBase".into(),
            field(ForeignRole::Base, &(BigUint::from_bytes_le(&raw) % &p)),
        ),
        (
            "rawScalar".into(),
            field(ForeignRole::Scalar, &(BigUint::from_bytes_le(&raw) % &q)),
        ),
        ("initialPoint".into(), identity.clone()),
        (
            "storedPointResult".into(),
            Value::Foreign(point_result.clone()).public_json(),
        ),
        (
            "mapPointResult".into(),
            Value::Foreign(point_result).public_json(),
        ),
        ("missingPointResult".into(), identity),
        (
            "guardedPointBytes".into(),
            json!({"kind":"bytes","values":identity_bytes}),
        ),
    ]);
    for (input, output) in [
        ("expectedBase", "baseResult"),
        ("expectedRawScalar", "rawScalar"),
        ("expectedPoint", "pointResult"),
    ] {
        supplied.insert(input.into(), expected[output].clone());
    }
    let execute = |inputs| {
        prepare(
            &plan,
            inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
    };
    let mut execution = execute(&supplied).unwrap();
    check(&execution, &circuit).unwrap();
    assert_eq!(execution.returns_json(), expected);
    assert_eq!(execution.preimage.private_transcript.len(), 73);
    let original = execution.preimage.public_transcript_outputs[0];
    execution.preimage.public_transcript_outputs[0] = original + Fr::from(1u64);
    assert!(check(&execution, &circuit).is_err());
    execution.preimage.public_transcript_outputs[0] = original;
    execution.preimage.private_transcript[72] = Fr::from(1u64);
    assert!(check(&execution, &circuit).is_err());
    execution.preimage.private_transcript[72] = Fr::from(0u64);
    let zero = ForeignValue::zero(ForeignType::new(
        ForeignFamily::Curve25519,
        ForeignRole::Base,
    ))
    .unwrap();
    execution.preimage.private_transcript[..2].copy_from_slice(&zero.encode().unwrap());
    assert!(check(&execution, &circuit).is_err());
    let mut active = supplied.clone();
    active.insert("decodeGuard".into(), json!(true));
    assert!(execute(&active).is_err());
    let mut zero_inverse = supplied.clone();
    zero_inverse.insert("base".into(), Value::Foreign(zero).public_json());
    assert!(execute(&zero_inverse).is_err());
}
