#![cfg(feature = "zkir-321")]

use noctium_runtime::{Db, Plan, check, create_state, field_value, prepare, zkir::IrSource};
use num_bigint::BigUint;
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};

const ORDER: &str = "6554484396890773809930967563523245729705921265872317281365359162392183254199";
const GENERATOR_TIMES_SEVEN_X: &str =
    "47805549206756120863994733988949966563868680443409072344285414365387721651928";
const GENERATOR_TIMES_SEVEN_Y: &str =
    "10883866336127360287053583923937114185802477515052223349661086820822299756070";

fn assert_outputs(state: &ChargedState<Db>) {
    let StateValue::Array(state) = state.get_ref() else {
        panic!("expected three output cells")
    };
    for (index, expected) in ["7", GENERATOR_TIMES_SEVEN_X, GENERATOR_TIMES_SEVEN_Y]
        .iter()
        .enumerate()
    {
        let StateValue::Cell(actual) = state.get(index).unwrap() else {
            panic!("expected output cell")
        };
        let expected = noctium_runtime::canonical_field(expected).unwrap();
        assert_eq!(**actual, field_value(expected));
    }
}

#[test]
#[ignore = "requires fresh JubjubScalarBoundary artifacts in NOCTIUM_JUBJUB_SCALAR_BOUNDARY_DIR"]
fn native_explicit_field_reduction_matches_compact_generator_multiplication() {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_JUBJUB_SCALAR_BOUNDARY_DIR")
            .expect("NOCTIUM_JUBJUB_SCALAR_BOUNDARY_DIR"),
    );
    let plan: Plan = serde_json::from_slice(
        &fs::read(directory.join("JubjubScalarBoundary.multiply.impact.json")).unwrap(),
    )
    .unwrap();
    let circuit_bytes = fs::read(directory.join("JubjubScalarBoundary.multiply.zkir")).unwrap();
    let circuit = IrSource::load(circuit_bytes.as_slice()).unwrap();
    let initial = create_state(
        &plan,
        &BTreeMap::from([
            ("reducedCell".into(), json!("0")),
            ("pointXCell".into(), json!("0")),
            ("pointYCell".into(), json!("0")),
        ]),
    )
    .unwrap();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let order = BigUint::parse_bytes(ORDER.as_bytes(), 10).unwrap();
    let cases = [BigUint::from(7u8), &order + BigUint::from(7u8)];
    let mut expected = None;

    for raw in cases {
        let inputs = BTreeMap::<String, Json>::from([("raw".into(), json!(raw.to_str_radix(10)))]);
        let execution = prepare(&plan, &inputs, &initial, parameters, address).unwrap();
        assert_eq!(
            check(&execution, &circuit).unwrap(),
            execution.activity_schedule
        );
        assert_outputs(&execution.after.state);
        if let Some(expected) = &expected {
            assert_eq!(execution.after.state, *expected, "q+7 must match 7");
        } else {
            expected = Some(execution.after.state.clone());
        }
    }
}
