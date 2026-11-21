#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{
    Db, Plan, Value, aggregates::Schema, check, create_state, field_decimal,
    merkle::merkle_tree_at, prepare, zkir::IrSource,
};
use onchain_runtime::state::ChargedState;
use serde_json::{Value as Json, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    env,
    fs::File,
    path::PathBuf,
};

type Fixture = (Plan, IrSource);

const APPEND_ROOT: &str =
    "28130625729914575041647056173685745844593451559868206617144826111893468892246";
const SPARSE_ROOT: &str =
    "17043442761246653451561963191561449650744055284151181557094286140959269003621";
const DEFAULT_ROOT: &str =
    "16246533595274911424894714064505090489952840905827103507406487792312255667120";

fn fixture(entry: &str) -> Fixture {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_TYPED_MERKLE_DIR")
            .expect("set fresh outputs in NOCTIUM_TYPED_MERKLE_DIR"),
    );
    let stem = format!("NativeTypedMerkleLeaves.{entry}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit =
        IrSource::load(File::open(directory.join(format!("{stem}.zkir"))).unwrap()).unwrap();
    (plan, circuit)
}

fn inputs(plan: &Plan, leaf: bool, position: u64, enabled: bool) -> BTreeMap<String, Json> {
    plan.circuit
        .inputs
        .iter()
        .map(|input| {
            let value = match input.name.as_str() {
                "owner" => json!({"kind":"bytes", "values":vec![7u8; 32]}),
                "leaf" => json!(leaf),
                "position" => json!(position.to_string()),
                "enabled" => json!(enabled),
                other => panic!("unexpected input {other}"),
            };
            (input.name.clone(), value)
        })
        .collect()
}

fn run(
    (plan, circuit): &Fixture,
    leaf: bool,
    position: u64,
    enabled: bool,
    state: &ChargedState<Db>,
) -> noctium_runtime::Execution {
    let execution = prepare(
        plan,
        &inputs(plan, leaf, position, enabled),
        state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .unwrap_or_else(|error| panic!("{}: {error}", plan.entrypoint));
    check(&execution, circuit).unwrap_or_else(|error| panic!("{}: {error}", plan.entrypoint));
    execution
}

fn assert_tree(
    plan: &Plan,
    state: &ChargedState<Db>,
    name: &str,
    keys: &[Value],
    expected_root: &str,
    expected_cursor: u64,
    expected_history: Option<&[&str]>,
) {
    let tree = merkle_tree_at(&plan.state, state, name, keys).unwrap();
    let view = tree.view().unwrap();
    assert_eq!(field_decimal(view.root), expected_root, "{name} root");
    assert_eq!(view.first_free, expected_cursor, "{name} cursor");
    if let Some(expected_history) = expected_history {
        let actual = tree
            .historic_roots()
            .unwrap()
            .map(|root| field_decimal(root.unwrap()))
            .collect::<BTreeSet<_>>();
        assert_eq!(
            actual,
            expected_history
                .iter()
                .map(|root| (*root).to_owned())
                .collect()
        );
    }
}

fn bool_schema() -> Schema {
    Schema::from_json(
        br#"{"schemaVersion":1,"typeFingerprint":"NoctiumCompositeTypeV1;sBNoctiumCompositeLayoutV1;0;0;","layout":{"kind":"scalar","leaf":{"kind":"bool"}},"counts":{"leaves":1,"expandedNodes":1,"layoutNodes":1}}"#,
    )
    .unwrap()
}

fn assert_bool_leaf(
    plan: &Plan,
    state: &ChargedState<Db>,
    name: &str,
    keys: &[Value],
    index: u64,
    value: bool,
) {
    let tree = merkle_tree_at(&plan.state, state, name, keys).unwrap();
    let leaf = serde_json::to_vec(&json!({"kind":"bool", "value":value})).unwrap();
    tree.structured_path(index, &bool_schema(), &leaf).unwrap();
}

#[test]
#[ignore = "requires fresh NativeTypedMerkleLeaves outputs in NOCTIUM_TYPED_MERKLE_DIR"]
fn typed_bool_merkle_leaves_match_compact_on_ordinary_and_historic_trees() {
    let setup = fixture("setup");
    let append = fixture("append");
    let set_index = fixture("setIndex");
    let set_default = fixture("setDefault");
    let initial = create_state(
        &setup.0,
        &BTreeMap::from([
            ("ordinary".into(), json!([])),
            ("archives".into(), json!([])),
        ]),
    )
    .unwrap();
    let owner = [Value::Bytes(vec![7; 32])];
    let initialized = run(&setup, false, 0, true, &initial).after.state;
    assert_tree(&setup.0, &initialized, "ordinary", &[], "0", 0, None);
    assert_tree(
        &setup.0,
        &initialized,
        "archives",
        &owner,
        "0",
        0,
        Some(&["0"]),
    );

    let appended = run(&append, true, 0, true, &initialized).after.state;
    assert_tree(&append.0, &appended, "ordinary", &[], APPEND_ROOT, 1, None);
    assert_tree(
        &append.0,
        &appended,
        "archives",
        &owner,
        APPEND_ROOT,
        1,
        Some(&["0", APPEND_ROOT]),
    );
    assert_bool_leaf(&append.0, &appended, "ordinary", &[], 0, true);
    assert_bool_leaf(&append.0, &appended, "archives", &owner, 0, true);

    let sparse = run(&set_index, true, 3, true, &appended).after.state;
    assert_tree(&set_index.0, &sparse, "ordinary", &[], SPARSE_ROOT, 4, None);
    assert_tree(
        &set_index.0,
        &sparse,
        "archives",
        &owner,
        SPARSE_ROOT,
        4,
        Some(&["0", APPEND_ROOT, SPARSE_ROOT]),
    );
    assert_bool_leaf(&set_index.0, &sparse, "ordinary", &[], 0, true);
    assert_bool_leaf(&set_index.0, &sparse, "ordinary", &[], 3, true);
    assert_bool_leaf(&set_index.0, &sparse, "archives", &owner, 0, true);
    assert_bool_leaf(&set_index.0, &sparse, "archives", &owner, 3, true);

    let defaulted = run(&set_default, false, 0, true, &sparse).after.state;
    assert_tree(
        &set_default.0,
        &defaulted,
        "ordinary",
        &[],
        DEFAULT_ROOT,
        4,
        None,
    );
    assert_tree(
        &set_default.0,
        &defaulted,
        "archives",
        &owner,
        DEFAULT_ROOT,
        4,
        Some(&["0", APPEND_ROOT, SPARSE_ROOT, DEFAULT_ROOT]),
    );
    assert_bool_leaf(&set_default.0, &defaulted, "ordinary", &[], 0, false);
    assert_bool_leaf(&set_default.0, &defaulted, "ordinary", &[], 3, true);
    assert_bool_leaf(&set_default.0, &defaulted, "archives", &owner, 0, false);
    assert_bool_leaf(&set_default.0, &defaulted, "archives", &owner, 3, true);
    assert!(
        merkle_tree_at(&set_default.0.state, &defaulted, "ordinary", &[])
            .unwrap()
            .structured_path(
                0,
                &bool_schema(),
                &serde_json::to_vec(&json!({"kind":"bool", "value":true})).unwrap()
            )
            .is_err()
    );

    let out_of_range = prepare(
        &set_index.0,
        &inputs(&set_index.0, true, 4, true),
        &defaulted,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    );
    assert!(out_of_range.is_err());

    let skipped = run(&set_index, false, 4, false, &defaulted);
    assert_eq!(skipped.after.state, defaulted);
}
