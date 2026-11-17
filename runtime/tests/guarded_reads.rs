#![cfg(feature = "zkir-321")]

use nightlean_runtime::{
    Db, Expr, Plan, check, create_state, field_decimal, field_value, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str = include_str!(
    "fixtures/generic-state/issue43-guarded-reads/321/Issue43GuardedReads.update.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "fixtures/generic-state/issue43-guarded-reads/321/Issue43GuardedReads.update.zkir"
);

fn plan() -> Plan {
    serde_json::from_str(PLAN).expect("source-generated guarded read plan parses")
}

fn state(plan: &Plan) -> ChargedState<Db> {
    create_state(
        plan,
        &BTreeMap::from([
            ("marker".to_owned(), json!("23")),
            ("balances".to_owned(), json!([])),
        ]),
    )
    .expect("source state creates native cells and empty map")
}

fn inputs(enabled: bool) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("account".to_owned(), json!("7")),
        ("enabled".to_owned(), json!(enabled)),
    ])
}

fn balance(state: &ChargedState<Db>, account: u64) -> Option<String> {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(map) = &*array.get(1).expect("map slot exists") else {
        panic!("expected state map")
    };
    let value = map.get(&field_value(Fr::from(account)))?;
    let StateValue::Cell(cell) = &*value else {
        panic!("expected map value cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    Some(field_decimal(fields[0]))
}

fn marker(state: &ChargedState<Db>) -> String {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Cell(cell) = &*array.get(0).expect("cell slot exists") else {
        panic!("expected state cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

fn execute(
    plan: &Plan,
    enabled: bool,
    initial: &ChargedState<Db>,
) -> anyhow::Result<nightlean_runtime::Execution> {
    prepare(
        plan,
        &inputs(enabled),
        initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
}

#[test]
fn guarded_reads_default_inactive_values_and_bind_current_native_reads() {
    let plan = plan();
    let circuit = IrSource::load(CIRCUIT).expect("source ZKIR parses");
    let initial = state(&plan);

    let active = execute(&plan, true, &initial)
        .expect("absent map read skips; initialization and later reads use ordered state");
    assert_eq!(balance(&active.after.state, 7).as_deref(), Some("99"));
    assert_eq!(marker(&active.after.state), "23");
    assert!(check(&active, &circuit).is_ok());

    let existing = execute(&plan, true, &active.after.state)
        .expect("existing map reads activate while the later membership/read default to zero");
    assert_eq!(balance(&existing.after.state, 7).as_deref(), Some("99"));
    assert!(check(&existing, &circuit).is_ok());

    let inactive_cell = execute(&plan, false, &initial)
        .expect("false cell read binds zero without reading the cell path");
    assert_eq!(
        balance(&inactive_cell.after.state, 7).as_deref(),
        Some("99")
    );
    assert!(check(&inactive_cell, &circuit).is_ok());

    let mut altered_guard = plan.clone();
    let missing_read = altered_guard
        .reads
        .iter_mut()
        .find(|read| read.name == "missingValue")
        .expect("guarded map read schema exists");
    missing_read.guard = Some(Expr::Bool { value: false });
    assert!(execute(&altered_guard, true, &initial).is_err());

    let mut altered_read = plan.clone();
    altered_read
        .reads
        .iter_mut()
        .find(|read| read.name == "skippedCell")
        .expect("guarded cell read schema exists")
        .name = "forgedCell".to_owned();
    assert!(execute(&altered_read, true, &initial).is_err());
}
