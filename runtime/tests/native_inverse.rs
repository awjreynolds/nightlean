#![cfg(feature = "zkir-321")]

use nightlean_runtime::{Db, Plan, check, create_state, field_value, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::{EmbeddedFr, Fr};

fn fixture(operation: &str) -> (Plan, IrSource) {
    let (plan, circuit): (&str, &[u8]) = match operation {
        "invert" => (
            include_str!("fixtures/native-inverse/321/NativeInverse.invert.impact.json"),
            include_bytes!("fixtures/native-inverse/321/NativeInverse.invert.zkir"),
        ),
        "discard" => (
            include_str!("fixtures/native-inverse/321/NativeInverse.discard.impact.json"),
            include_bytes!("fixtures/native-inverse/321/NativeInverse.discard.zkir"),
        ),
        "guarded" => (
            include_str!("fixtures/native-inverse/321/NativeInverse.guarded.impact.json"),
            include_bytes!("fixtures/native-inverse/321/NativeInverse.guarded.zkir"),
        ),
        _ => unreachable!(),
    };
    (
        serde_json::from_str(plan).unwrap(),
        IrSource::load(circuit).unwrap(),
    )
}
fn inputs(native: u64, scalar: u64, enabled: Option<bool>) -> BTreeMap<String, Json> {
    let mut values = BTreeMap::from([
        ("denominator".into(), json!(native.to_string())),
        (
            "scalar".into(),
            json!({"kind":"jubjubScalar","value":scalar.to_string()}),
        ),
    ]);
    if let Some(enabled) = enabled {
        values.insert("enabled".into(), json!(enabled));
    }
    values
}
fn results(state: &ChargedState<Db>, native: Fr, scalar: Fr) {
    let StateValue::Array(state) = state.get_ref() else {
        panic!("expected state array")
    };
    for (index, expected) in [native, scalar].iter().enumerate() {
        let StateValue::Cell(actual) = state.get(index).unwrap() else {
            panic!("expected field cell")
        };
        assert_eq!(**actual, field_value(*expected));
    }
}

#[test]
fn native_and_scalar_inverse_keep_zero_rejection_and_safe_inactive_guards() {
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let native_inverse = Fr::from(1u64) / Fr::from(7u64);
    let scalar_inverse = Fr::try_from(EmbeddedFr::from(1u64) / EmbeddedFr::from(5u64)).unwrap();
    for operation in ["invert", "discard", "guarded"] {
        let (plan, circuit) = fixture(operation);
        let initial = create_state(
            &plan,
            &BTreeMap::from([
                ("nativeResult".into(), json!("0")),
                ("scalarResult".into(), json!("0")),
            ]),
        )
        .unwrap();
        let enabled = (operation == "guarded").then_some(true);
        let valid = prepare(&plan, &inputs(7, 5, enabled), &initial, params, address).unwrap();
        check(&valid, &circuit).unwrap();
        if operation == "discard" {
            results(&valid.after.state, Fr::from(0u64), Fr::from(0u64));
        } else {
            results(&valid.after.state, native_inverse, scalar_inverse);
        }
        for (native, scalar) in [(0, 5), (7, 0)] {
            if let Ok(invalid) = prepare(
                &plan,
                &inputs(native, scalar, enabled),
                &initial,
                params,
                address,
            ) {
                assert!(check(&invalid, &circuit).is_err());
            }
        }
        if operation == "guarded" {
            let inactive =
                prepare(&plan, &inputs(0, 0, Some(false)), &initial, params, address).unwrap();
            check(&inactive, &circuit).unwrap();
            results(&inactive.after.state, Fr::from(0u64), Fr::from(0u64));
        }
    }
}
