#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{
    Db, Plan, check, create_state, field_decimal, merkle::merkle_tree_at, prepare, zkir::IrSource,
};
use onchain_runtime::state::ChargedState;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs::File, path::PathBuf};

type Fixture = (Plan, IrSource);

fn fixture(entry: &str) -> Fixture {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_JUBJUB_MERKLE_DIR")
            .expect("set fresh outputs in NOCTIUM_JUBJUB_MERKLE_DIR"),
    );
    let stem = format!("JubjubMerkleLeaves.{entry}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit =
        IrSource::load(File::open(directory.join(format!("{stem}.zkir"))).unwrap()).unwrap();
    (plan, circuit)
}

fn identity_vector() -> ([u8; 32], String) {
    let vectors: Vec<Json> = serde_json::from_str(include_str!(
        "fixtures/merkle-curve-leaves/compact-0.36.1.json"
    ))
    .unwrap();
    let vector = vectors
        .iter()
        .find(|vector| {
            vector["leaf"]["kind"] == "jubjubPoint"
                && vector["leaf"]["x"] == "0"
                && vector["leaf"]["y"] == "1"
        })
        .expect("pinned Compact identity point vector");
    let digest: [u8; 32] = hex::decode(vector["leafHash"].as_str().unwrap())
        .unwrap()
        .try_into()
        .unwrap();
    (digest, vector["root"].as_str().unwrap().to_owned())
}

fn inputs(plan: &Plan, position: u64, enabled: bool) -> BTreeMap<String, Json> {
    plan.circuit
        .inputs
        .iter()
        .map(|input| {
            let value = match input.name.as_str() {
                "point" => json!({"kind":"jubjubPoint", "x":"0", "y":"1"}),
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

fn assert_identity_tree(fixture: &Fixture, state: &ChargedState<Db>) {
    let (digest, expected_root) = identity_vector();
    let tree = merkle_tree_at(&fixture.0.state, state, "points", &[]).unwrap();
    let view = tree.view().unwrap();
    assert_eq!(field_decimal(view.root), expected_root);
    assert_eq!(view.first_free, 1);
    let stored = tree.prehashed_path(0, digest).unwrap();
    assert_eq!(stored.leaf_hash(), &digest);
    assert_eq!(stored.root(), view.root);
}

#[test]
#[ignore = "requires fresh JubjubMerkleLeaves outputs in NOCTIUM_JUBJUB_MERKLE_DIR"]
fn jubjub_point_append_and_indexed_default_match_compact_identity_vector() {
    let append = fixture("append");
    let append_at = fixture("appendAt");
    let default_at = fixture("defaultAt");
    let initial = create_state(&append.0, &BTreeMap::from([("points".into(), json!([]))])).unwrap();

    let appended = run(&append, 0, true, &initial).after.state;
    assert_identity_tree(&append, &appended);

    let indexed = run(&append_at, 0, true, &initial).after.state;
    assert_identity_tree(&append_at, &indexed);

    let defaulted = run(&default_at, 0, true, &initial).after.state;
    assert_identity_tree(&default_at, &defaulted);
}
