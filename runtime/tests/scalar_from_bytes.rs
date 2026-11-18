#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Expr, MODULUS, Plan, ScalarType, check, create_state, prepare, zkir::IrSource,
};
use num_bigint::BigUint;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

const PLAN: &str =
    include_str!("fixtures/scalar-from-bytes/321/ScalarFromBytes.decode.impact.json");
const CIRCUIT: &[u8] = include_bytes!("fixtures/scalar-from-bytes/321/ScalarFromBytes.decode.zkir");
const JUBJUB_ORDER: &str =
    "6554484396890773809930967563523245729705921265872317281365359162392183254199";

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn private_index(plan: &Plan, name: &str) -> usize {
    plan.circuit
        .inputs
        .iter()
        .filter(|input| input.visibility == "private")
        .take_while(|input| input.name != name)
        .map(|input| {
            ScalarType::parse(&input.ty)
                .unwrap()
                .bytes_length()
                .unwrap_or(1)
        })
        .sum()
}

#[test]
fn scalar_decoders_reduce_full_byte_values_and_keep_empty_operand_assertions() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let before = initial.clone();
    let wide = vec![255u8; 64];
    let maximum: Vec<_> = (0..1024).map(|index| (index % 256) as u8).collect();
    let modulus = BigUint::parse_bytes(MODULUS.as_bytes(), 10).unwrap();
    let scalar_order = BigUint::parse_bytes(JUBJUB_ORDER.as_bytes(), 10).unwrap();
    let wide_integer = BigUint::from_bytes_le(&wide);
    assert_ne!(
        &wide_integer % &scalar_order,
        (&wide_integer % &modulus) % &scalar_order
    );
    let supplied = BTreeMap::from([
        ("wide64".into(), bytes(&wide)),
        ("maximum1024".into(), bytes(&maximum)),
        ("empty0".into(), bytes(&[])),
        ("nativeEnabled".into(), json!(true)),
        ("scalarEnabled".into(), json!(true)),
    ]);
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let execution = prepare(&plan, &supplied, &initial, params, address).unwrap();
    assert_eq!(
        check(&execution, &circuit).unwrap(),
        execution.activity_schedule
    );
    assert_eq!(execution.preimage.private_transcript.len(), 1090);
    let expected = BTreeMap::from([
        (
            "native64".into(),
            json!((&wide_integer % &modulus).to_str_radix(10)),
        ),
        (
            "scalar64".into(),
            json!((&wide_integer % &scalar_order).to_str_radix(10)),
        ),
        (
            "native1024".into(),
            json!((BigUint::from_bytes_le(&maximum) % &modulus).to_str_radix(10)),
        ),
        (
            "scalar1024".into(),
            json!((BigUint::from_bytes_le(&maximum) % &scalar_order).to_str_radix(10)),
        ),
        ("emptyNative".into(), json!("0")),
        ("emptyScalar".into(), json!("0")),
    ]);
    assert_eq!(execution.returns_json(), expected);
    assert_eq!(initial, before);
    assert_eq!(execution.after.state, initial);

    for guard in ["nativeEnabled", "scalarEnabled"] {
        let mut disabled = supplied.clone();
        disabled.insert(guard.into(), json!(false));
        assert!(prepare(&plan, &disabled, &initial, params, address).is_err());
        let mut altered = prepare(&plan, &supplied, &initial, params, address).unwrap();
        altered.preimage.private_transcript[private_index(&plan, guard)] = Fr::from(0u64);
        assert!(check(&altered, &circuit).is_err());
    }
    let mut changed = prepare(&plan, &supplied, &initial, params, address).unwrap();
    changed.preimage.private_transcript[0] = Fr::from(256u64);
    assert!(check(&changed, &circuit).is_err());
    let mut forged = plan.clone();
    forged.returns[0].expression = Expr::Constant { value: "0".into() };
    let forged = prepare(&forged, &supplied, &initial, params, address).unwrap();
    assert!(check(&forged, &circuit).is_err());
    for (name, length) in [("wide64", 63), ("maximum1024", 1025), ("empty0", 1)] {
        let mut invalid = supplied.clone();
        invalid.insert(name.into(), bytes(&vec![0; length]));
        assert!(prepare(&plan, &invalid, &initial, params, address).is_err());
    }
}
