#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{
    Db, Plan, aggregates::Schema, check, create_state, field_decimal, merkle::merkle_tree_at,
    prepare, zkir::IrSource,
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
    "41498041122156615907734201443800972360403159218673782910906735168768629395736";
const SPARSE_ROOT: &str =
    "40354775844647557467683646849622796372373223037362699614063017930900206276343";
const DEFAULT_ROOT: &str =
    "37209924186628564446821313957374143838394805355827780640358174939144179734266";

fn fixture(entry: &str) -> Fixture {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_RECORD_MERKLE_DIR")
            .expect("set fresh outputs in NOCTIUM_RECORD_MERKLE_DIR"),
    );
    let stem = format!("NativeRecordMerkleLeaves.{entry}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit =
        IrSource::load(File::open(directory.join(format!("{stem}.zkir"))).unwrap()).unwrap();
    (plan, circuit)
}

fn inputs(plan: &Plan, position: u64, enabled: bool) -> BTreeMap<String, Json> {
    plan.circuit
        .inputs
        .iter()
        .map(|input| {
            let value = match input.name.as_str() {
                "tag" => json!({"kind":"bytes", "values":[12, 0, 0]}),
                "accepted" => json!(true),
                "count" => json!("258"),
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
    position: u64,
    enabled: bool,
    state: &ChargedState<Db>,
) -> noctium_runtime::Execution {
    let execution = prepare(
        plan,
        &inputs(plan, position, enabled),
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
    expected_root: &str,
    expected_cursor: u64,
    expected_history: Option<&[&str]>,
) {
    let tree = merkle_tree_at(&plan.state, state, name, &[]).unwrap();
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

fn record_schema() -> Schema {
    Schema::from_json(
        br#"{"schemaVersion":1,"typeFingerprint":"NoctiumCompositeTypeV1;t3;[b3;sBsU65535;]NoctiumCompositeLayoutV1;0;0;","layout":{"kind":"tuple","items":[{"kind":"bytes","length":3},{"kind":"scalar","leaf":{"kind":"bool"}},{"kind":"scalar","leaf":{"kind":"uint","maximum":"65535"}}]},"counts":{"leaves":5,"expandedNodes":7,"layoutNodes":4}}"#,
    )
    .unwrap()
}

fn assert_record_leaf(
    plan: &Plan,
    state: &ChargedState<Db>,
    name: &str,
    index: u64,
    tag: [u8; 3],
    accepted: bool,
    count: u16,
) {
    let tree = merkle_tree_at(&plan.state, state, name, &[]).unwrap();
    let leaf = serde_json::to_vec(&json!({
        "kind":"tuple",
        "items":[
            {"kind":"bytes", "values":tag},
            {"kind":"bool", "value":accepted},
            {"kind":"uint", "maximum":"65535", "value":count.to_string()}
        ]
    }))
    .unwrap();
    tree.structured_path(index, &record_schema(), &leaf)
        .unwrap();
}

#[test]
#[ignore = "requires fresh NativeRecordMerkleLeaves outputs in NOCTIUM_RECORD_MERKLE_DIR"]
fn record_merkle_leaves_match_compact_on_ordinary_and_historic_trees() {
    let append = fixture("append");
    let set_index = fixture("setIndex");
    let set_default = fixture("setDefault");
    let initial = create_state(
        &append.0,
        &BTreeMap::from([
            ("ordinary".into(), json!([])),
            ("archive".into(), json!([])),
        ]),
    )
    .unwrap();

    assert_tree(&append.0, &initial, "ordinary", "0", 0, None);
    assert_tree(&append.0, &initial, "archive", "0", 0, Some(&["0"]));

    let appended = run(&append, 0, true, &initial).after.state;
    assert_tree(&append.0, &appended, "ordinary", APPEND_ROOT, 1, None);
    assert_tree(
        &append.0,
        &appended,
        "archive",
        APPEND_ROOT,
        1,
        Some(&["0", APPEND_ROOT]),
    );
    assert_record_leaf(&append.0, &appended, "ordinary", 0, [12, 0, 0], true, 258);
    assert_record_leaf(&append.0, &appended, "archive", 0, [12, 0, 0], true, 258);

    let sparse = run(&set_index, 3, true, &appended).after.state;
    assert_tree(&set_index.0, &sparse, "ordinary", SPARSE_ROOT, 4, None);
    assert_tree(
        &set_index.0,
        &sparse,
        "archive",
        SPARSE_ROOT,
        4,
        Some(&["0", APPEND_ROOT, SPARSE_ROOT]),
    );
    for name in ["ordinary", "archive"] {
        assert_record_leaf(&set_index.0, &sparse, name, 0, [12, 0, 0], true, 258);
        assert_record_leaf(&set_index.0, &sparse, name, 3, [12, 0, 0], true, 258);
    }

    let defaulted = run(&set_default, 0, true, &sparse).after.state;
    assert_tree(
        &set_default.0,
        &defaulted,
        "ordinary",
        DEFAULT_ROOT,
        4,
        None,
    );
    assert_tree(
        &set_default.0,
        &defaulted,
        "archive",
        DEFAULT_ROOT,
        4,
        Some(&["0", APPEND_ROOT, SPARSE_ROOT, DEFAULT_ROOT]),
    );
    for name in ["ordinary", "archive"] {
        assert_record_leaf(&set_default.0, &defaulted, name, 0, [0, 0, 0], false, 0);
        assert_record_leaf(&set_default.0, &defaulted, name, 3, [12, 0, 0], true, 258);
    }

    let rejected = prepare(
        &set_index.0,
        &inputs(&set_index.0, 4, true),
        &defaulted,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    );
    assert!(rejected.is_err());

    let skipped = run(&set_index, 4, false, &defaulted);
    assert_eq!(skipped.after.state, defaulted);
}
