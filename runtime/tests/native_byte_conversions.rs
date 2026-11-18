#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Db, MODULUS, Plan, check, create_state, field_decimal, field_value, prepare, zkir::IrSource,
};
use num_bigint::BigUint;
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine, Fr};

fn fixture(operation: &str) -> (Plan, IrSource) {
    let (plan, circuit): (&str, &[u8]) = match operation {
        "convert" => (
            include_str!(
                "fixtures/native-byte-conversions/321/NativeByteConversions.convert.impact.json"
            ),
            include_bytes!(
                "fixtures/native-byte-conversions/321/NativeByteConversions.convert.zkir"
            ),
        ),
        "discard" => (
            include_str!(
                "fixtures/native-byte-conversions/321/NativeByteConversions.discard.impact.json"
            ),
            include_bytes!(
                "fixtures/native-byte-conversions/321/NativeByteConversions.discard.zkir"
            ),
        ),
        "guarded" => (
            include_str!(
                "fixtures/native-byte-conversions/321/NativeByteConversions.guarded.impact.json"
            ),
            include_bytes!(
                "fixtures/native-byte-conversions/321/NativeByteConversions.guarded.zkir"
            ),
        ),
        _ => unreachable!(),
    };
    (
        serde_json::from_str(plan).unwrap(),
        IrSource::load(circuit).unwrap(),
    )
}
fn encoded(point: EmbeddedGroupAffine) -> [u8; 32] {
    let mut bytes: [u8; 32] = point.y().unwrap().as_le_bytes().try_into().unwrap();
    bytes[31] |= (point.x().unwrap().as_le_bytes()[0] & 1) << 7;
    bytes
}
fn bytes(value: &[u8; 32]) -> Json {
    json!({"kind":"bytes","values":value.as_slice()})
}
fn inputs(
    operation: &str,
    point_raw: &[u8; 32],
    field_raw: &[u8; 32],
    enabled: bool,
) -> BTreeMap<String, Json> {
    let mut inputs = BTreeMap::from([("pointRaw".into(), bytes(point_raw))]);
    if operation == "guarded" {
        inputs.insert("enabled".into(), json!(enabled));
    }
    if operation == "convert" {
        let native = Fr::from(0u64) - Fr::from(1u64);
        let scalar = EmbeddedFr::from(0u64) - EmbeddedFr::from(1u64);
        let point = EmbeddedGroupAffine::generator() * EmbeddedFr::from(7u64);
        inputs.insert("native".into(), json!(field_decimal(native)));
        inputs.insert("scalar".into(),json!({"kind":"jubjubScalar","value":BigUint::from_bytes_le(&scalar.as_le_bytes()).to_str_radix(10)}));
        inputs.insert("point".into(),json!({"kind":"jubjubPoint","x":field_decimal(point.x().unwrap()),"y":field_decimal(point.y().unwrap())}));
        inputs.insert("fieldRaw".into(), bytes(field_raw));
    }
    inputs
}
fn results(state: &ChargedState<Db>, expected: &[Fr; 4]) {
    let StateValue::Array(state) = state.get_ref() else {
        panic!("expected state array")
    };
    for (index, expected) in expected.iter().enumerate() {
        let StateValue::Cell(actual) = state.get(index).unwrap() else {
            panic!("expected field cell")
        };
        assert_eq!(**actual, field_value(*expected));
    }
}

#[test]
fn typed_byte_conversions_reduce_fields_and_preserve_point_domain_checks() {
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let point = EmbeddedGroupAffine::generator() * EmbeddedFr::from(9u64);
    let point_raw = encoded(point);
    let field_raw = [255u8; 32];
    let native =
        BigUint::from_bytes_le(&field_raw) % BigUint::parse_bytes(MODULUS.as_bytes(), 10).unwrap();
    let native = Fr::from_le_bytes(&native.to_bytes_le()).unwrap();
    let scalar = Fr::try_from(EmbeddedFr::from_le_bytes_wide(&field_raw).unwrap()).unwrap();
    let mut negative_zero = [0; 32];
    negative_zero[0] = 1;
    negative_zero[31] = 128;
    for operation in ["convert", "discard", "guarded"] {
        let (plan, circuit) = fixture(operation);
        let initial = create_state(
            &plan,
            &BTreeMap::from([
                ("nativeResult".into(), json!("0")),
                ("scalarResult".into(), json!("0")),
                ("xResult".into(), json!("0")),
                ("yResult".into(), json!("0")),
            ]),
        )
        .unwrap();
        let valid = prepare(
            &plan,
            &inputs(operation, &point_raw, &field_raw, true),
            &initial,
            params,
            address,
        )
        .unwrap();
        check(&valid, &circuit).unwrap();
        match operation {
            "convert" => results(
                &valid.after.state,
                &[native, scalar, point.x().unwrap(), point.y().unwrap()],
            ),
            "discard" => results(&valid.after.state, &[Fr::from(0u64); 4]),
            _ => results(
                &valid.after.state,
                &[
                    Fr::from(0u64),
                    Fr::from(0u64),
                    point.x().unwrap(),
                    point.y().unwrap(),
                ],
            ),
        }
        for invalid in [[255; 32], negative_zero, [0; 32]] {
            if let Ok(rejected) = prepare(
                &plan,
                &inputs(operation, &invalid, &field_raw, true),
                &initial,
                params,
                address,
            ) {
                assert!(check(&rejected, &circuit).is_err());
            }
        }
        if operation == "guarded" {
            let inactive = prepare(
                &plan,
                &inputs(operation, &[255; 32], &field_raw, false),
                &initial,
                params,
                address,
            )
            .unwrap();
            check(&inactive, &circuit).unwrap();
            results(&inactive.after.state, &[Fr::from(0u64); 4]);
        }
        if operation == "convert" {
            let identity = encoded(EmbeddedGroupAffine::identity());
            let canonical = prepare(
                &plan,
                &inputs(operation, &identity, &[0; 32], true),
                &initial,
                params,
                address,
            )
            .unwrap();
            check(&canonical, &circuit).unwrap();
            results(
                &canonical.after.state,
                &[
                    Fr::from(0u64),
                    Fr::from(0u64),
                    Fr::from(0u64),
                    Fr::from(1u64),
                ],
            );
        }
    }
}
