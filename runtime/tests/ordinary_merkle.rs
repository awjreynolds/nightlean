#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Db, Execution, Plan, check, create_state, field_decimal, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value, json};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::fab::AlignedValueExt;

#[test]
#[ignore = "requires fresh Lean output set via NOCTIUM_NATIVE_TEST_ARTIFACTS"]
fn ordinary_merkle_appends_match_compact_and_reset_exactly() {
    let artifacts = PathBuf::from(std::env::var_os("NOCTIUM_NATIVE_TEST_ARTIFACTS").unwrap());
    let fixture = |entry| {
        let prefix = format!("NativeMerkleTree.{entry}");
        let plan: Plan = serde_json::from_slice(
            &fs::read(artifacts.join(format!("{prefix}.impact.json"))).unwrap(),
        )
        .unwrap();
        let relation =
            IrSource::load(fs::File::open(artifacts.join(format!("{prefix}.zkir"))).unwrap())
                .unwrap();
        (plan, relation)
    };
    let address = coin_structure::contract::ContractAddress::default();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let run = |plan: &Plan,
               circuit: &IrSource,
               args: BTreeMap<String, Value>,
               state: &ChargedState<Db>| {
        let execution = prepare(plan, &args, state, params, address).unwrap();
        check(&execution, circuit).unwrap();
        execution
    };
    let (append, circuit) = fixture("append");
    let initial = create_state(&append, &BTreeMap::from([("claims".into(), json!([]))])).unwrap();
    let (full_status, full_circuit) = fixture("fullStatus");
    let read = |state: &ChargedState<Db>| -> Execution {
        run(&full_status, &full_circuit, BTreeMap::new(), state)
    };
    assert_eq!(read(&initial).returns_json()["fullStatus"], false);
    let mut state = initial.clone();
    let args = |byte| {
        BTreeMap::from([(
            "leafHash".into(),
            json!({"kind":"bytes","values":vec![byte;32]}),
        )])
    };

    // Root sequence from the pinned Compact OrdinaryMerkle fixture.
    let roots = [
        "17029979906787068148615464077443109129720490673751283300379954364685288014954",
        "45137749480565895385758122683212244915529195091359138341472597836969923504049",
        "25117124299835895250907896203532552792670032528542297288772531067357116679580",
        "47912772248769352372635417155431636398353714911972954164866311838310133535619",
    ];
    for (index, expected_root) in roots.into_iter().enumerate() {
        let call = run(&append, &circuit, args(index + 1), &state);
        assert_eq!(call.returns_json()["fullStatus"], index == 3);
        state = call.after.state;
        let StateValue::Array(slots) = state.get_ref() else {
            panic!("expected contract state array")
        };
        let StateValue::Array(node) = slots.get(0).unwrap() else {
            panic!("expected Merkle state array")
        };
        let StateValue::BoundedMerkleTree(tree) = node.get(0).unwrap() else {
            panic!("expected native tree")
        };
        let StateValue::Cell(cursor) = node.get(1).unwrap() else {
            panic!("expected Merkle cursor")
        };
        let mut cursor_fields = Vec::new();
        cursor.value_only_field_repr(&mut cursor_fields);
        assert_eq!(cursor_fields.len(), 1);
        assert_eq!(field_decimal(cursor_fields[0]), (index + 1).to_string());
        assert_eq!(field_decimal(tree.root().unwrap().0), expected_root);
    }
    let mut full = read(&state);
    assert_eq!(full.returns_json()["fullStatus"], true);
    full.preimage.public_transcript_outputs[0] = 0u64.into();
    assert!(check(&full, &full_circuit).is_err());
    let Err(error) = prepare(&append, &args(5), &state, params, address) else {
        panic!("the fifth append must fail")
    };
    assert!(error.to_string().contains("MerkleTree is full"));

    let (reset, reset_circuit) = fixture("resetAndCheck");
    let reset_result = run(&reset, &reset_circuit, BTreeMap::new(), &state);
    assert_eq!(reset_result.returns_json()["resetStatus"], false);
    assert_eq!(reset_result.after.state, initial);
}
