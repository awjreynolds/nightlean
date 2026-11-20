#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{
    Db, Execution, Plan, check, create_state, field_decimal, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::PathBuf,
};
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

fn fixture(entry: &str) -> (Plan, IrSource) {
    let dir = PathBuf::from(std::env::var_os("NOCTIUM_NATIVE_TEST_ARTIFACTS").unwrap());
    let stem = format!("NativeHistoricMerkle.{entry}");
    (
        serde_json::from_slice(&fs::read(dir.join(format!("{stem}.impact.json"))).unwrap())
            .unwrap(),
        IrSource::load(fs::File::open(dir.join(format!("{stem}.zkir"))).unwrap()).unwrap(),
    )
}

fn run(
    (plan, circuit): &(Plan, IrSource),
    inputs: BTreeMap<String, Value>,
    state: &ChargedState<Db>,
) -> Execution {
    let result = prepare(
        plan,
        &inputs,
        state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .unwrap_or_else(|error| panic!("{}: {error}", plan.entrypoint));
    check(&result, circuit).unwrap_or_else(|error| panic!("{}: {error}", plan.entrypoint));
    result
}

fn snapshot(state: &ChargedState<Db>) -> (String, String, BTreeSet<String>) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected state slots")
    };
    let StateValue::Array(node) = slots.get(0).unwrap() else {
        panic!("expected historic tree state")
    };
    let StateValue::BoundedMerkleTree(tree) = node.get(0).unwrap() else {
        panic!("expected native Merkle tree")
    };
    let StateValue::Cell(cursor) = node.get(1).unwrap() else {
        panic!("expected append cursor")
    };
    let StateValue::Map(history) = node.get(2).unwrap() else {
        panic!("expected historic root map")
    };
    let mut count = Vec::new();
    cursor.value_only_field_repr(&mut count);
    assert_eq!(count.len(), 1);
    let roots = history
        .iter()
        .map(|entry| {
            let (key, value) = &*entry;
            assert!(matches!(**value, StateValue::Null));
            let mut fields = Vec::new();
            key.value_only_field_repr(&mut fields);
            assert_eq!(fields.len(), 1);
            field_decimal(fields[0])
        })
        .collect();
    (
        field_decimal(tree.root().unwrap().0),
        field_decimal(count[0]),
        roots,
    )
}

const FIRST_ROOT: &str =
    "17029979906787068148615464077443109129720490673751283300379954364685288014954";

#[test]
#[ignore = "requires fresh Lean output set via NOCTIUM_NATIVE_TEST_ARTIFACTS"]
fn historic_merkle_writes_and_resets_match_pinned_compact() {
    let append_hash = fixture("appendHash");
    let append_field = fixture("appendField");
    let index_hash = fixture("writeHashIndex");
    let index_field = fixture("writeFieldIndex");
    let checker = fixture("checkDigest");
    let append_and_check = fixture("appendAndCheck");
    let clear_history = fixture("clearHistory");
    let guarded_clear = fixture("guardedClearHistory");
    let reset = fixture("resetTree");
    let initial =
        create_state(&checker.0, &BTreeMap::from([("claims".into(), json!([]))])).unwrap();
    let check_digest = |digest: &str, state: &ChargedState<Db>| {
        let input = BTreeMap::from([("expectedRoot".into(), json!(digest))]);
        let call = run(&checker, input, state);
        assert_eq!(&call.after.state, state);
        call
    };
    let mut first = check_digest("0", &initial);
    assert_eq!(first.returns_json()["knownRoot"], true);
    assert_eq!(first.preimage.public_transcript_outputs[0], Fr::from(1u64));
    first.preimage.public_transcript_outputs[0] = Fr::from(0u64);
    assert!(check(&first, &checker.1).is_err());
    assert_eq!(
        check_digest("1", &initial).returns_json()["knownRoot"],
        false
    );

    let hash = |byte| json!({"kind":"bytes","values":vec![byte;32]});
    for (digest, expected) in [(FIRST_ROOT, true), ("0", true), ("1", false)] {
        let call = run(
            &append_and_check,
            BTreeMap::from([
                ("expectedRoot".into(), json!(digest)),
                ("leafHash".into(), hash(1)),
            ]),
            &initial,
        );
        assert_eq!(call.returns_json()["knownRoot"], expected);
    }

    let writes = [
        (
            &append_hash,
            BTreeMap::from([("leafHash".into(), hash(1))]),
            "1",
            FIRST_ROOT,
        ),
        (
            &append_field,
            BTreeMap::from([("leaf".into(), json!("256"))]),
            "2",
            "6931440650487741251506177490939322727222034237805487103764299892108796170176",
        ),
        (
            &index_hash,
            BTreeMap::from([
                ("position".into(), json!("3")),
                ("leafHash".into(), hash(2)),
            ]),
            "4",
            "38100625729571630659924408805965211666395418313173951873944772350958507857729",
        ),
        (
            &index_field,
            BTreeMap::from([("position".into(), json!("0")), ("leaf".into(), json!("0"))]),
            "4",
            "46499618928865373917898407405712784146599776628838439995200923554029685295528",
        ),
    ];
    let mut state = initial.clone();
    let mut history = BTreeSet::from(["0".to_owned()]);
    for (operation, inputs, cursor, root) in writes {
        state = run(operation, inputs, &state).after.state;
        history.insert(root.to_owned());
        assert_eq!(
            snapshot(&state),
            (root.into(), cursor.into(), history.clone())
        );
        for digest in &history {
            let read = check_digest(digest, &state);
            assert_eq!(read.returns_json()["knownRoot"], true);
            assert_eq!(read.returns_json()["fullStatus"], cursor == "4");
        }
    }
    assert!(
        prepare(
            &index_hash.0,
            &BTreeMap::from([
                ("position".into(), json!("4")),
                ("leafHash".into(), hash(1)),
            ]),
            &state,
            &INITIAL_PARAMETERS,
            ContractAddress::default()
        )
        .is_err()
    );

    let (tip, cursor, _) = snapshot(&state);
    let cleared = run(&clear_history, BTreeMap::new(), &state).after.state;
    assert_eq!(
        snapshot(&cleared),
        (tip.clone(), cursor, BTreeSet::from([tip.clone()]))
    );
    for digest in history {
        assert_eq!(
            check_digest(&digest, &cleared).returns_json()["knownRoot"],
            digest == tip
        );
    }
    for (active, prior, expected) in [(false, &state, true), (true, &cleared, false)] {
        let call = run(
            &guarded_clear,
            BTreeMap::from([
                ("active".into(), json!(active)),
                ("expectedRoot".into(), json!("0")),
            ]),
            &state,
        );
        assert_eq!(call.returns_json()["knownRoot"], expected);
        assert_eq!(&call.after.state, prior);
    }
    let reset_state = run(&reset, BTreeMap::new(), &cleared).after.state;
    assert_eq!(reset_state, initial);
    assert_eq!(
        snapshot(&reset_state),
        ("0".into(), "0".into(), BTreeSet::from(["0".into()]))
    );
}
