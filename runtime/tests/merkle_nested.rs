#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{
    Db, Execution, Plan, check, create_state, field_decimal, field_value, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::PathBuf,
};
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

type Fixture = (Plan, IrSource);
type Path = (u8, u64);

fn fixture(entry: &str) -> Fixture {
    let dir = PathBuf::from(std::env::var_os("NOCTIUM_NATIVE_TEST_ARTIFACTS").unwrap());
    let name = format!("NativeNestedMerkle.{entry}");
    (
        serde_json::from_slice(&fs::read(dir.join(format!("{name}.impact.json"))).unwrap())
            .unwrap(),
        IrSource::load(fs::File::open(dir.join(format!("{name}.zkir"))).unwrap()).unwrap(),
    )
}

fn bytes(byte: u8) -> Value {
    json!({"kind": "bytes", "values": vec![byte; 32]})
}

fn path_args((owner, bucket): Path) -> BTreeMap<String, Value> {
    BTreeMap::from([
        ("owner".into(), bytes(owner)),
        ("bucket".into(), json!(bucket.to_string())),
    ])
}

fn write_args(path: Path, hash: u8, leaf: u64) -> BTreeMap<String, Value> {
    let mut args = path_args(path);
    args.insert("leafHash".into(), bytes(hash));
    args.insert("leaf".into(), json!(leaf.to_string()));
    args
}

fn indexed_args(path: Path, hash: u8, leaf: u64, position: u64) -> BTreeMap<String, Value> {
    let mut args = write_args(path, hash, leaf);
    args.insert("position".into(), json!(position.to_string()));
    args
}

fn evaluate(
    plan: &Plan,
    args: BTreeMap<String, Value>,
    state: &ChargedState<Db>,
) -> anyhow::Result<Execution> {
    prepare(
        plan,
        &args,
        state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
}

fn run(
    (plan, circuit): &Fixture,
    args: BTreeMap<String, Value>,
    state: &ChargedState<Db>,
) -> Execution {
    let execution =
        evaluate(plan, args, state).unwrap_or_else(|error| panic!("{}: {error}", plan.entrypoint));
    check(&execution, circuit).unwrap_or_else(|error| panic!("{}: {error}", plan.entrypoint));
    execution
}

fn stored_tree(state: &ChargedState<Db>, slot: usize, (owner, bucket): Path) -> StateValue<Db> {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected state slots")
    };
    let StateValue::Map(owners) = slots.get(slot).unwrap() else {
        panic!("expected outer map")
    };
    let parent = owners.get(&AlignedValue::from([owner; 32])).unwrap();
    let StateValue::Map(buckets) = &*parent else {
        panic!("expected inner map")
    };
    (*buckets.get(&field_value(Fr::from(bucket))).unwrap()).clone()
}

fn snapshot(
    state: &ChargedState<Db>,
    path: Path,
    ordinary: (&str, &str),
    historic: (&str, &str),
    history: &[&str],
) {
    for (slot, (cursor, root)) in [ordinary, historic].into_iter().enumerate() {
        let StateValue::Array(ref tree) = stored_tree(state, slot, path) else {
            panic!("expected tree array")
        };
        let StateValue::BoundedMerkleTree(digest) = tree.get(0).unwrap() else {
            panic!("expected bounded tree")
        };
        let StateValue::Cell(count) = tree.get(1).unwrap() else {
            panic!("expected cursor")
        };
        let mut fields = Vec::new();
        count.value_only_field_repr(&mut fields);
        assert_eq!(fields.len(), 1);
        assert_eq!(field_decimal(fields[0]), cursor);
        assert_eq!(field_decimal(digest.root().unwrap().0), root);
        if slot == 1 {
            let StateValue::Map(roots) = tree.get(2).unwrap() else {
                panic!("expected history")
            };
            let actual = roots
                .iter()
                .map(|entry| {
                    let (key, value) = &*entry;
                    assert!(matches!(**value, StateValue::Null));
                    let mut fields = Vec::new();
                    key.value_only_field_repr(&mut fields);
                    assert_eq!(fields.len(), 1);
                    field_decimal(fields[0])
                })
                .collect::<BTreeSet<_>>();
            assert_eq!(actual, history.iter().map(|root| (*root).into()).collect());
        }
    }
}

#[test]
#[ignore = "requires fresh Lean output set via NOCTIUM_NATIVE_TEST_ARTIFACTS"]
fn nested_merkle_operations_match_compact_and_preserve_siblings() {
    let setup = fixture("setup");
    let setup_and_append = fixture("setupAndAppend");
    let append = fixture("append");
    let indexed = fixture("setIndex");
    let read = fixture("readTrees");
    let clear = fixture("clear");
    let reset = fixture("resetTrees");
    let initial = create_state(
        &setup.0,
        &BTreeMap::from([
            ("ordinary".into(), json!([])),
            ("archives".into(), json!([])),
        ]),
    )
    .unwrap();
    let selected = (7, 1);
    let sibling = (7, 2);
    let other = (8, 1);
    let read_args = |digest: &str| {
        let mut args = path_args(selected);
        args.insert("digest".into(), json!(digest));
        args
    };
    let compare = |state: &ChargedState<Db>, digest, expected: [bool; 4]| {
        let call = run(&read, read_args(digest), state);
        for (name, want) in [
            "ordinaryKnown",
            "archiveKnown",
            "ordinaryFull",
            "archiveFull",
        ]
        .into_iter()
        .zip(expected)
        {
            assert_eq!(call.returns_json()[name], want, "{name}");
        }
        assert_eq!(&call.after.state, state);
        call
    };
    assert!(evaluate(&read.0, read_args("0"), &initial).is_err());
    assert!(evaluate(&reset.0, path_args(selected), &initial).is_err());
    let initial_history =
        "35694116202192454536022596311527311726911393046632366691736512928127990181458";
    let after_append = (
        "1",
        "17029979906787068148615464077443109129720490673751283300379954364685288014954",
    );
    let mut state = run(&setup_and_append, write_args(selected, 1, 1), &initial)
        .after
        .state;
    snapshot(
        &state,
        selected,
        after_append,
        ("1", initial_history),
        &["0", initial_history],
    );
    for (path, hash, leaf) in [(sibling, 2, 256), (other, 4, 257)] {
        state = run(&setup, path_args(path), &state).after.state;
        state = run(&append, write_args(path, hash, leaf), &state)
            .after
            .state;
    }
    snapshot(
        &state,
        selected,
        after_append,
        ("1", initial_history),
        &["0", initial_history],
    );
    let neighboring_trees = |state: &ChargedState<Db>| {
        [
            stored_tree(state, 0, sibling),
            stored_tree(state, 1, sibling),
            stored_tree(state, 0, other),
            stored_tree(state, 1, other),
        ]
    };
    let untouched = neighboring_trees(&state);
    let ordinary_index =
        "24384193648268865082143763383430680137169643988677567459801776720386725274219";
    let historic_index =
        "28177993292845671258227895926917860147375346170730846347234185481881467288296";
    state = run(&indexed, indexed_args(selected, 3, 0, 3), &state)
        .after
        .state;
    snapshot(
        &state,
        selected,
        ("3", ordinary_index),
        ("4", historic_index),
        &["0", initial_history, historic_index],
    );
    compare(&state, initial_history, [false, true, false, true]);
    let mut read_tampered = compare(&state, ordinary_index, [true, false, false, true]);
    assert_eq!(
        read_tampered.preimage.public_transcript_outputs[0],
        Fr::from(1u64)
    );
    read_tampered.preimage.public_transcript_outputs[0] = Fr::from(0u64);
    assert!(check(&read_tampered, &read.1).is_err());
    assert!(evaluate(&indexed.0, indexed_args(selected, 4, 1, 4), &state).is_err());

    let ordinary_tip =
        "26990056723722507304411228356670923454980478117046661243568979107406641904749";
    let historic_tip =
        "29036963130611229309623637016472689056242148956693383472438437097059567070516";
    state = run(&indexed, indexed_args(selected, 5, 256, 3), &state)
        .after
        .state;
    snapshot(
        &state,
        selected,
        ("3", ordinary_tip),
        ("4", historic_tip),
        &["0", initial_history, historic_index, historic_tip],
    );
    compare(&state, historic_index, [false, true, false, true]);
    state = run(&clear, path_args(selected), &state).after.state;
    snapshot(
        &state,
        selected,
        ("3", ordinary_tip),
        ("4", historic_tip),
        &[historic_tip],
    );
    compare(&state, initial_history, [false, false, false, true]);
    compare(&state, historic_tip, [false, true, false, true]);
    assert_eq!(neighboring_trees(&state), untouched);
    state = run(&reset, path_args(selected), &state).after.state;
    snapshot(&state, selected, ("0", "0"), ("0", "0"), &["0"]);
    compare(&state, "0", [true, true, false, false]);
    assert_eq!(neighboring_trees(&state), untouched);
}
