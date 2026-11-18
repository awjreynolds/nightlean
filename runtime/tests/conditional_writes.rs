#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Db, Expr, Instruction, Plan, check, create_state, field_decimal, field_value, prepare,
    zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;
use transient_crypto::fab::AlignedValueExt;

const PLAN: &str =
    include_str!("fixtures/generic-state/issue43/321/Issue43ConditionalWrites.apply.impact.json");
const CIRCUIT: &[u8] =
    include_bytes!("fixtures/generic-state/issue43/321/Issue43ConditionalWrites.apply.zkir");

fn plan() -> Plan {
    serde_json::from_str(PLAN).expect("source-generated guarded-write plan parses")
}

fn state(plan: &Plan) -> ChargedState<Db> {
    create_state(
        plan,
        &BTreeMap::from([
            ("current".to_owned(), json!("4")),
            ("allowances".to_owned(), json!([])),
        ]),
    )
    .expect("source state creates native ledger state")
}

fn inputs(enabled: bool) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("enabled".to_owned(), json!(enabled)),
        ("account".to_owned(), json!("7")),
    ])
}

fn current(state: &ChargedState<Db>) -> String {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Cell(cell) = &*array.get(0).expect("cell slot exists") else {
        panic!("expected cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

fn allowance(state: &ChargedState<Db>, account: u64) -> Option<String> {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(map) = &*array.get(1).expect("map slot exists") else {
        panic!("expected map")
    };
    let value = map.get(&field_value(Fr::from(account)))?;
    let StateValue::Cell(cell) = &*value else {
        panic!("expected map cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    Some(field_decimal(fields[0]))
}

fn execute(plan: &Plan, enabled: bool, initial: &ChargedState<Db>) -> noctium_runtime::Execution {
    prepare(
        plan,
        &inputs(enabled),
        initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .expect("guarded writes pass native state preparation")
}

#[test]
fn source_guarded_cell_and_map_writes_match_native_activity() {
    let plan = plan();
    let initial = state(&plan);
    let circuit = IrSource::load(CIRCUIT).expect("source ZKIR parses");

    let active = execute(&plan, true, &initial);
    assert_eq!(active.program.len(), 9);
    assert_eq!(current(&active.after.state), "21");
    assert_eq!(allowance(&active.after.state, 7).as_deref(), Some("9"));
    assert_eq!(check(&active, &circuit).unwrap(), active.activity_schedule);

    let inactive = execute(&plan, false, &initial);
    assert_eq!(inactive.program.len(), 2);
    assert_eq!(current(&inactive.after.state), "4");
    assert_eq!(allowance(&inactive.after.state, 7), None);
    assert_eq!(
        check(&inactive, &circuit).unwrap(),
        [None, None, Some(5), Some(5), Some(1), Some(4), Some(5), Some(5), Some(1)]
    );

    let mut altered_guard = plan.clone();
    for operation in altered_guard.operations.iter_mut().skip(2).take(3) {
        let Instruction::Guarded { guard, .. } = operation else {
            panic!("guarded cell operation exists")
        };
        *guard = Expr::Bool { value: false };
    }
    let mismatched = execute(&altered_guard, true, &initial);
    assert!(check(&mismatched, &circuit).is_err());

    let mut altered_transcript = execute(&plan, true, &initial);
    let last = altered_transcript
        .preimage
        .public_transcript_inputs
        .last_mut()
        .expect("active writes bind public transcript fields");
    *last = Fr::from(22u64);
    assert!(check(&altered_transcript, &circuit).is_err());
}
