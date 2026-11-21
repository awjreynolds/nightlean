#![cfg(feature = "zkir-321")]

use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env,
    path::{Path, PathBuf},
};

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_OPTIONAL_LIST_HEAD_DIR")
        .map(PathBuf::from)
        .expect("set fresh outputs in NOCTIUM_OPTIONAL_LIST_HEAD_DIR")
}

fn fixture(directory: &Path, entry: &str) -> (Plan, IrSource) {
    let stem = format!("OptionalListHead.{entry}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit = IrSource::load(
        std::fs::read(directory.join(format!("{stem}.zkir")))
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    (plan, circuit)
}

fn inputs(owner: u8, spender: u8, x: u64, y: u64, enabled: bool) -> BTreeMap<String, Json> {
    BTreeMap::from([
        (
            "owner".into(),
            json!({"kind":"bytes", "values":vec![owner; 32]}),
        ),
        (
            "spender".into(),
            json!({"kind":"bytes", "values":vec![spender; 32]}),
        ),
        ("x".into(), json!(x.to_string())),
        ("y".into(), json!(y.to_string())),
        ("enabled".into(), json!(enabled)),
    ])
}

fn assert_head(execution: &noctium_runtime::Execution, present: bool, x: &str, y: &str) {
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("present".into(), json!(present)),
            ("first".into(), json!(x)),
            ("second".into(), json!(y)),
        ])
    );
}

#[test]
#[ignore = "requires fresh OptionalListHead ledger outputs in NOCTIUM_OPTIONAL_LIST_HEAD_DIR"]
fn optional_list_head_defaults_only_empty_or_inactive_reads() {
    let directory = artifacts();
    let (seed, seed_circuit) = fixture(&directory, "seed");
    let (inspect_inbox, inbox_circuit) = fixture(&directory, "inspectInbox");
    let (inspect_path, path_circuit) = fixture(&directory, "inspectPath");
    let (inspect_guarded, guarded_circuit) = fixture(&directory, "inspectGuarded");
    let initial = create_state(
        &seed,
        &BTreeMap::from([("inbox".into(), json!([])), ("records".into(), json!([]))]),
    )
    .unwrap();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    let empty = prepare(
        &inspect_inbox,
        &inputs(1, 2, 0, 0, true),
        &initial,
        parameters,
        address,
    )
    .unwrap();
    check(&empty, &inbox_circuit).unwrap();
    assert_head(&empty, false, "0", "0");

    let zero_record = prepare(
        &seed,
        &inputs(1, 2, 0, 0, true),
        &initial,
        parameters,
        address,
    )
    .unwrap();
    check(&zero_record, &seed_circuit).unwrap();
    let state = zero_record.after.state;
    let present_zero = prepare(
        &inspect_inbox,
        &inputs(1, 2, 0, 0, true),
        &state,
        parameters,
        address,
    )
    .unwrap();
    check(&present_zero, &inbox_circuit).unwrap();
    assert_head(&present_zero, true, "0", "0");

    let nested_record = prepare(
        &seed,
        &inputs(7, 9, 41, 43, true),
        &state,
        parameters,
        address,
    )
    .unwrap();
    check(&nested_record, &seed_circuit).unwrap();
    let state = nested_record.after.state;
    let nested = prepare(
        &inspect_path,
        &inputs(7, 9, 0, 0, true),
        &state,
        parameters,
        address,
    )
    .unwrap();
    check(&nested, &path_circuit).unwrap();
    assert_head(&nested, true, "41", "43");

    let inactive_missing = prepare(
        &inspect_guarded,
        &inputs(8, 9, 0, 0, false),
        &state,
        parameters,
        address,
    )
    .unwrap();
    check(&inactive_missing, &guarded_circuit).unwrap();
    assert_head(&inactive_missing, false, "0", "0");

    assert!(
        prepare(
            &inspect_path,
            &inputs(8, 9, 0, 0, true),
            &state,
            parameters,
            address,
        )
        .is_err(),
        "active reads of absent nested map paths must fail"
    );

    let StateValue::Array(root) = initial.get_ref() else {
        panic!("expected contract state array");
    };
    let StateValue::Array(inbox) = root.get(0).expect("inbox slot exists") else {
        panic!("expected native List array");
    };
    let malformed_inbox = StateValue::Array(
        inbox
            .insert(0, inbox.get(2).expect("List length exists").clone())
            .unwrap(),
    );
    let malformed_state =
        ChargedState::new(StateValue::Array(root.insert(0, malformed_inbox).unwrap()));
    assert!(
        prepare(
            &inspect_inbox,
            &inputs(1, 2, 0, 0, true),
            &malformed_state,
            parameters,
            address,
        )
        .is_err(),
        "a non-null empty List sentinel must be rejected"
    );
}
