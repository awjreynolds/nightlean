#![cfg(feature = "zkir-321")]

use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom};
use noctium_runtime::{
    Db, Plan, Value, check, create_state, field_decimal, field_value, merkle::merkle_tree_at,
    prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env,
    path::{Path, PathBuf},
};
use storage::arena::Sp;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const BOOL_TRUE_ROOT: &str =
    "28130625729914575041647056173685745844593451559868206617144826111893468892246";

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_NATIVE_MAP_DEFAULT_DIR")
        .map(PathBuf::from)
        .expect("set fresh outputs in NOCTIUM_NATIVE_MAP_DEFAULT_DIR")
}

fn fixture(directory: &Path, entry: &str) -> (Plan, IrSource) {
    let stem = format!("NativeMapDefault.{entry}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit =
        IrSource::load(std::fs::File::open(directory.join(format!("{stem}.zkir"))).unwrap())
            .unwrap();
    (plan, circuit)
}

fn inputs(plan: &Plan, key: u64, amount: u64, enabled: bool) -> BTreeMap<String, Json> {
    plan.circuit
        .inputs
        .iter()
        .map(|input| {
            let value = match input.name.as_str() {
                "owner" => json!({"kind":"bytes", "values":vec![7u8; 32]}),
                "key" => json!(key.to_string()),
                "amount" => json!(amount.to_string()),
                "enabled" => json!(enabled),
                "leaf" => json!(true),
                other => panic!("unexpected input {other}"),
            };
            (input.name.clone(), value)
        })
        .collect()
}

fn run(
    plan: &Plan,
    circuit: &IrSource,
    key: u64,
    amount: u64,
    enabled: bool,
    state: &ChargedState<Db>,
) -> noctium_runtime::Execution {
    let execution = prepare(
        plan,
        &inputs(plan, key, amount, enabled),
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, circuit).unwrap();
    execution
}

fn state_slot<'a>(state: &'a ChargedState<Db>, plan: &Plan, name: &str) -> &'a StateValue<Db> {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected native state slots")
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == name)
        .expect("declared state slot");
    slots.get(slot).expect("state slot exists")
}

fn field(value: &AlignedValue) -> Fr {
    let mut fields = Vec::new();
    value.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    fields[0]
}

fn assert_scalar_map(
    state: &ChargedState<Db>,
    plan: &Plan,
    expected_size: usize,
    key: u64,
    value: u64,
) {
    let StateValue::Map(values) = state_slot(state, plan, "values") else {
        panic!("expected scalar Map")
    };
    assert_eq!(values.size(), expected_size);
    let stored = values
        .get(&field_value(Fr::from(key)))
        .expect("requested scalar Map entry");
    let StateValue::Cell(stored) = &*stored else {
        panic!("expected scalar Map cell")
    };
    assert_eq!(**stored, field_value(Fr::from(value)));
}

fn assert_empty_scalar_map(state: &ChargedState<Db>, plan: &Plan) {
    let StateValue::Map(values) = state_slot(state, plan, "values") else {
        panic!("expected scalar Map")
    };
    assert_eq!(values.size(), 0);
    assert!(values.get(&field_value(Fr::from(1u64))).is_none());
    assert!(values.get(&field_value(Fr::from(2u64))).is_none());
}

fn owner_map(state: &ChargedState<Db>, plan: &Plan, name: &str) -> Sp<StateValue<Db>> {
    let StateValue::Map(owners) = state_slot(state, plan, name) else {
        panic!("expected outer owner Map")
    };
    let owner: AlignedValue = [7u8; 32].into();
    owners.get(&owner).expect("owner entry exists")
}

fn assert_zero_counter(value: &StateValue<Db>) {
    let StateValue::Cell(counter) = value else {
        panic!("expected Counter cell")
    };
    assert_eq!(
        counter.alignment,
        Alignment::singleton(AlignmentAtom::Bytes { length: 8 })
    );
    assert_eq!(field(counter), Fr::from(0u64));
}

fn assert_merkle_default(value: &StateValue<Db>, historic: bool) {
    let StateValue::Array(tree) = value else {
        panic!("expected MerkleTree array")
    };
    assert_eq!(tree.len(), if historic { 3 } else { 2 });
    assert!(matches!(
        tree.get(0),
        Some(StateValue::BoundedMerkleTree(_))
    ));
    assert_zero_counter(tree.get(1).expect("MerkleTree cursor"));
    if historic {
        let StateValue::Map(history) = tree.get(2).expect("HistoricMerkleTree history") else {
            panic!("expected historic root map")
        };
        assert_eq!(history.size(), 0);
    }
}

fn historic_snapshot(plan: &Plan, state: &ChargedState<Db>) -> (String, u64, BTreeMap<String, ()>) {
    let path = [Value::Bytes(vec![7u8; 32])];
    let tree = merkle_tree_at(&plan.state, state, "historic", &path).unwrap();
    let view = tree.view().unwrap();
    let roots = tree
        .historic_roots()
        .unwrap()
        .map(|root| (field_decimal(root.unwrap()), ()))
        .collect();
    (field_decimal(view.root), view.first_free, roots)
}

fn empty_state(plan: &Plan) -> ChargedState<Db> {
    create_state(
        plan,
        &[
            "values",
            "nestedValues",
            "nestedMaps",
            "sets",
            "lists",
            "counters",
            "ordinary",
            "historic",
            "records",
        ]
        .into_iter()
        .map(|name| (name.to_owned(), json!([])))
        .collect(),
    )
    .unwrap()
}

#[test]
#[ignore = "requires fresh NativeMapDefault outputs in NOCTIUM_NATIVE_MAP_DEFAULT_DIR"]
fn native_map_default_inserts_replaces_and_initializes_typed_values() {
    let directory = artifacts();
    let (seed, seed_circuit) = fixture(&directory, "seed");
    let (default, default_circuit) = fixture(&directory, "defaultValue");
    let (clear, clear_circuit) = fixture(&directory, "clear");
    let (defaults, defaults_circuit) = fixture(&directory, "defaults");
    let (missing_parent, missing_parent_circuit) = fixture(&directory, "missingParent");
    let initial = empty_state(&seed);

    let first_default = run(&default, &default_circuit, 1, 0, true, &initial);
    assert_eq!(
        first_default.returns_json(),
        BTreeMap::from([
            ("hasEntry".into(), json!(true)),
            ("entries".into(), json!("1")),
            ("stored".into(), json!("0")),
        ])
    );
    assert_scalar_map(&first_default.after.state, &default, 1, 1, 0);

    let seeded = run(
        &seed,
        &seed_circuit,
        2,
        19,
        true,
        &first_default.after.state,
    );
    assert_eq!(
        seeded.returns_json(),
        BTreeMap::from([
            ("hasEntry".into(), json!(true)),
            ("entries".into(), json!("2")),
            ("stored".into(), json!("19")),
        ])
    );
    assert_scalar_map(&seeded.after.state, &seed, 2, 2, 19);

    let replaced = run(&default, &default_circuit, 2, 0, true, &seeded.after.state);
    assert_eq!(
        replaced.returns_json(),
        BTreeMap::from([
            ("hasEntry".into(), json!(true)),
            ("entries".into(), json!("2")),
            ("stored".into(), json!("0")),
        ])
    );
    assert_scalar_map(&replaced.after.state, &default, 2, 2, 0);
    assert_scalar_map(&replaced.after.state, &default, 2, 1, 0);

    let cleared = run(&clear, &clear_circuit, 1, 0, false, &replaced.after.state);
    assert_eq!(
        cleared.returns_json(),
        BTreeMap::from([
            ("hasEntry".into(), json!(false)),
            ("entries".into(), json!("0")),
        ])
    );
    assert_empty_scalar_map(&cleared.after.state, &clear);

    let missing_parent_skipped = run(
        &missing_parent,
        &missing_parent_circuit,
        3,
        0,
        false,
        &cleared.after.state,
    );
    assert_eq!(missing_parent_skipped.after.state, cleared.after.state);
    assert!(
        prepare(
            &missing_parent,
            &inputs(&missing_parent, 3, 0, true),
            &cleared.after.state,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .is_err()
    );

    let inactive = run(
        &defaults,
        &defaults_circuit,
        4,
        0,
        false,
        &cleared.after.state,
    );
    let owner: AlignedValue = [7u8; 32].into();
    let StateValue::Map(records) = state_slot(&inactive.after.state, &defaults, "records") else {
        panic!("expected record Map")
    };
    assert!(records.get(&owner).is_none());

    let active = run(
        &defaults,
        &defaults_circuit,
        4,
        0,
        true,
        &inactive.after.state,
    );
    let nested_values = owner_map(&active.after.state, &defaults, "nestedValues");
    let StateValue::Map(nested) = &*nested_values else {
        panic!("expected nested scalar Map")
    };
    let nested_value = nested
        .get(&field_value(Fr::from(4u64)))
        .expect("nested default exists");
    let StateValue::Cell(nested_value) = &*nested_value else {
        panic!("expected nested scalar cell")
    };
    assert_eq!(**nested_value, field_value(Fr::from(0u64)));

    let nested_map = owner_map(&active.after.state, &defaults, "nestedMaps");
    assert!(matches!(&*nested_map, StateValue::Map(map) if map.size() == 0));
    let set = owner_map(&active.after.state, &defaults, "sets");
    assert!(matches!(&*set, StateValue::Map(map) if map.size() == 0));
    let list_value = owner_map(&active.after.state, &defaults, "lists");
    let StateValue::Array(list) = &*list_value else {
        panic!("expected empty List")
    };
    assert_eq!(list.len(), 3);
    assert!(matches!(list.get(0), Some(StateValue::Null)));
    assert!(matches!(list.get(1), Some(StateValue::Null)));
    assert_eq!(
        field(match list.get(2).unwrap() {
            StateValue::Cell(length) => length,
            _ => panic!("expected List length cell"),
        }),
        Fr::from(0u64)
    );
    let counter = owner_map(&active.after.state, &defaults, "counters");
    assert_zero_counter(&counter);
    let ordinary = owner_map(&active.after.state, &defaults, "ordinary");
    assert_merkle_default(&ordinary, false);
    let historic = owner_map(&active.after.state, &defaults, "historic");
    assert_merkle_default(&historic, true);

    let record_value = owner_map(&active.after.state, &defaults, "records");
    let StateValue::Cell(record) = &*record_value else {
        panic!("expected default record cell")
    };
    let amount = field_value(Fr::from(0u64));
    let payload: AlignedValue = [0u8; 32].into();
    let identity_x = field_value(Fr::from(0u64));
    let identity_y = field_value(Fr::from(1u64));
    assert_eq!(
        **record,
        AlignedValue::concat([&amount, &payload, &identity_x, &identity_y])
    );

    let (check_zero, check_zero_circuit) = fixture(&directory, "checkHistoricZero");
    let check_zero = |state: &ChargedState<Db>| {
        let returns = run(&check_zero, &check_zero_circuit, 0, 0, false, state).returns_json();
        returns["known"].as_bool().unwrap()
    };
    assert_eq!(check_zero(&active.after.state), false);

    let (append_historic, append_historic_circuit) = fixture(&directory, "appendHistoric");
    let appended = run(
        &append_historic,
        &append_historic_circuit,
        0,
        0,
        true,
        &active.after.state,
    );
    assert_eq!(
        historic_snapshot(&append_historic, &appended.after.state),
        (
            BOOL_TRUE_ROOT.to_owned(),
            1,
            BTreeMap::from([(BOOL_TRUE_ROOT.to_owned(), ())]),
        )
    );
    assert_eq!(check_zero(&appended.after.state), false);

    let (default_historic, default_historic_circuit) = fixture(&directory, "defaultHistoric");
    let cleared = run(
        &default_historic,
        &default_historic_circuit,
        0,
        0,
        false,
        &appended.after.state,
    );
    assert_eq!(
        historic_snapshot(&default_historic, &cleared.after.state),
        ("0".into(), 0, BTreeMap::new())
    );
    assert_eq!(check_zero(&cleared.after.state), false);

    let (reset_historic, reset_historic_circuit) = fixture(&directory, "resetHistoric");
    let reset = run(
        &reset_historic,
        &reset_historic_circuit,
        0,
        0,
        false,
        &cleared.after.state,
    );
    assert_eq!(
        historic_snapshot(&reset_historic, &reset.after.state),
        ("0".into(), 0, BTreeMap::from([("0".into(), ())]))
    );
    assert_eq!(check_zero(&reset.after.state), true);
}
