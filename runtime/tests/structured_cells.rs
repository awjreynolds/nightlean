#![cfg(feature = "zkir-321")]

use noctium_runtime::{Db, Plan, check, create_state, field_decimal, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str = include_str!("fixtures/structured-cells/321/StructuredCells.update.impact.json");
const CIRCUIT: &[u8] = include_bytes!("fixtures/structured-cells/321/StructuredCells.update.zkir");

fn inputs(enabled: bool, amount: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("enabled".into(), json!(enabled)),
        ("amount".into(), json!(amount.to_string())),
    ])
}

fn balance(state: &ChargedState<Db>) -> String {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected contract state array");
    };
    let StateValue::Cell(cell) = &*array.get(0).expect("balance cell exists") else {
        panic!("expected balance cell");
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

#[test]
fn helper_body_reads_and_writes_guarded_native_cell_state() {
    let plan: Plan = serde_json::from_str(PLAN).expect("source ledger plan parses");
    let circuit = IrSource::load(CIRCUIT).expect("source ZKIR parses");
    let initial = create_state(&plan, &BTreeMap::from([("balance".into(), json!("3"))]))
        .expect("initial balance state parses");
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    let active = prepare(&plan, &inputs(true, 7), &initial, params, address)
        .expect("active helper branch prepares");
    check(&active, &circuit).expect("active helper branch relation checks");
    assert_eq!(balance(&active.after.state), "10");
    assert_eq!(
        active.returns_json(),
        BTreeMap::from([("result".into(), json!("10"))])
    );

    let inactive = prepare(&plan, &inputs(false, 8), &initial, params, address)
        .expect("inactive helper branch skips its narrowing cast and state effects");
    check(&inactive, &circuit).expect("inactive helper branch relation checks");
    assert_eq!(inactive.after.state, initial);
    assert_eq!(balance(&inactive.after.state), "3");
    assert_eq!(
        inactive.returns_json(),
        BTreeMap::from([("result".into(), json!("3"))])
    );

    if let Ok(invalid_active) = prepare(&plan, &inputs(true, 8), &initial, params, address) {
        assert!(check(&invalid_active, &circuit).is_err());
    }

    let mut altered_guard = inactive;
    altered_guard.preimage.private_transcript[0] = Fr::from(1u64);
    assert!(check(&altered_guard, &circuit).is_err());
}
