#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Db, Instruction, Plan, PreparationCursor, PreparationStep, Value, check, create_state,
    field_decimal, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str =
    include_str!("fixtures/preparation-cursor/321/NativePreparationCursor.advance.impact.json");
const CIRCUIT: &[u8] =
    include_bytes!("fixtures/preparation-cursor/321/NativePreparationCursor.advance.zkir");

fn initial_state(plan: &Plan) -> ChargedState<Db> {
    create_state(plan, &BTreeMap::from([("balance".into(), json!("3"))]))
        .expect("initial balance state creates")
}

fn input(expected: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([("expected".into(), json!(expected.to_string()))])
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

fn assert_before_balance(read: &noctium_runtime::PreparationRead) -> u64 {
    assert!(read.active);
    assert_eq!(read.values.len(), 1);
    assert_eq!(
        read.values.get("beforeBalance"),
        Some(&Value::Native(Fr::from(3u64)))
    );
    let Value::Native(value) = read.values["beforeBalance"] else {
        panic!("expected a Native ledger balance");
    };
    field_decimal(value).parse().expect("small fixture balance")
}

#[test]
fn preparation_cursor_requests_private_input_after_the_state_read() {
    let plan: Plan = serde_json::from_str(PLAN).expect("source plan parses");
    let circuit = IrSource::load(CIRCUIT).expect("source ZKIR parses");
    let initial = initial_state(&plan);
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let mut cursor = PreparationCursor::new(&plan, &input(10), &initial, params, address)
        .expect("cursor accepts the declared public input while private delta is absent");
    let mut saw_before_balance = false;
    let mut supplied_delta = false;
    let mut provider_delta: Option<u64> = None;
    let mut saw_after_balance = false;

    loop {
        match cursor.step().expect("preparation step succeeds") {
            PreparationStep::PendingInputs(missing) => {
                assert!(
                    saw_before_balance,
                    "ledger state is observed before requesting its witness"
                );
                assert!(!supplied_delta);
                assert_eq!(
                    missing
                        .iter()
                        .map(|item| item.name.as_str())
                        .collect::<Vec<_>>(),
                    vec!["delta"]
                );
                let delta = provider_delta
                    .take()
                    .expect("provider receives the ledger read");
                cursor
                    .supply_inputs(&BTreeMap::from([(
                        "delta".into(),
                        json!(delta.to_string()),
                    )]))
                    .expect("provider supplies its result derived from the ledger read");
                supplied_delta = true;
            }
            PreparationStep::Operation { read, .. } => {
                if let Some(read) = read {
                    match read.name.as_str() {
                        "beforeBalance" => {
                            assert!(!saw_before_balance);
                            provider_delta = Some(assert_before_balance(&read) + 4);
                            saw_before_balance = true;
                        }
                        "afterBalance" => {
                            assert!(supplied_delta);
                            assert_eq!(read.values.len(), 1);
                            assert_eq!(
                                read.values.get("afterBalance"),
                                Some(&Value::Native(Fr::from(10u64)))
                            );
                            saw_after_balance = true;
                        }
                        _ => {}
                    }
                }
            }
            PreparationStep::Complete => break,
        }
    }

    assert!(saw_before_balance && supplied_delta && saw_after_balance);
    let execution = cursor.finish().expect("completed cursor yields execution");
    check(&execution, &circuit).expect("native relation accepts the completed preparation");
    assert_eq!(balance(&execution.after.state), "10");
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([("observed".into(), json!("10"))])
    );
}

#[test]
fn preparation_cursor_rejects_incomplete_and_non_atomic_input_batches() {
    let plan: Plan = serde_json::from_str(PLAN).expect("source plan parses");
    let initial = initial_state(&plan);
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let public = input(10);
    let mut invalid_schema = plan.clone();
    invalid_schema
        .circuit
        .inputs
        .iter_mut()
        .find(|input| input.name == "delta")
        .unwrap()
        .ty = "Unknown".into();
    assert!(PreparationCursor::new(&invalid_schema, &public, &initial, params, address).is_err());
    let mut incomplete =
        PreparationCursor::new(&plan, &public, &initial, params, address).expect("cursor starts");
    let mut saw_before_balance = false;
    loop {
        match incomplete.step().expect("cursor reaches pending input") {
            PreparationStep::Operation {
                read: Some(read), ..
            } if read.name == "beforeBalance" => {
                assert_before_balance(&read);
                saw_before_balance = true;
            }
            PreparationStep::PendingInputs(missing) => {
                assert!(saw_before_balance);
                assert_eq!(missing.len(), 1);
                assert!(incomplete.finish().is_err());
                break;
            }
            PreparationStep::Operation { .. } => {}
            PreparationStep::Complete => panic!("cursor completed without its private input"),
        }
    }

    let mut cursor = PreparationCursor::new(&plan, &public, &initial, params, address)
        .expect("a fresh cursor starts after incomplete finish rejection");
    let mut saw_before_balance = false;
    loop {
        match cursor.step().expect("cursor reaches pending input") {
            PreparationStep::Operation {
                read: Some(read), ..
            } if read.name == "beforeBalance" => {
                assert_before_balance(&read);
                saw_before_balance = true;
            }
            PreparationStep::PendingInputs(missing) => {
                assert!(saw_before_balance);
                assert_eq!(missing.len(), 1);
                break;
            }
            PreparationStep::Operation { .. } => {}
            PreparationStep::Complete => panic!("cursor completed without its private input"),
        }
    }

    assert!(
        cursor
            .supply_inputs(&BTreeMap::from([
                ("delta".into(), json!("7")),
                ("unexpected".into(), json!("1")),
            ]))
            .is_err()
    );
    assert!(
        cursor
            .supply_inputs(&BTreeMap::from([("delta".into(), json!(true))]))
            .is_err()
    );
    assert!(
        cursor
            .supply_inputs(&BTreeMap::from([
                ("delta".into(), json!("7")),
                ("expected".into(), json!("11")),
            ]))
            .is_err()
    );
    assert!(
        cursor
            .supply_inputs(&BTreeMap::from([("delta".into(), json!("7"))]))
            .is_ok()
    );

    let mut invalid_plan = plan.clone();
    invalid_plan.operations[0] = Instruction::Insert { n: 0 };
    let mut invalid = PreparationCursor::new(&invalid_plan, &public, &initial, params, address)
        .expect("cursor binds inputs before evaluating the malformed operation");
    assert!(
        invalid.step().is_err(),
        "invalid native insertion depth rejects"
    );
    assert!(
        invalid.step().is_err(),
        "a failed preparation cursor stays poisoned"
    );
    assert!(invalid.finish().is_err());
}
