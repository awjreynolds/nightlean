#![cfg(feature = "zkir-321")]

use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use noctium_runtime::{Db, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    fs::File,
    path::{Path, PathBuf},
};
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

fn artifacts() -> PathBuf {
    PathBuf::from(
        std::env::var_os("NOCTIUM_OPAQUE_MAP_DIR")
            .expect("set fresh OpaqueByteMap outputs in NOCTIUM_OPAQUE_MAP_DIR"),
    )
}

fn fixture(directory: &Path, entry: &str) -> (Plan, IrSource) {
    let stem = format!("OpaqueByteMap.{entry}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit =
        IrSource::load(File::open(directory.join(format!("{stem}.zkir"))).unwrap()).unwrap();
    (plan, circuit)
}

fn inputs(key: &[u8; 32], payload: Option<&[u8]>) -> BTreeMap<String, Json> {
    let mut values = BTreeMap::from([(
        "key".into(),
        json!({"kind":"bytes", "values":key.as_slice()}),
    )]);
    if let Some(payload) = payload {
        values.insert(
            "payload".into(),
            json!({"kind":"opaqueBytes", "values":payload}),
        );
    }
    values
}

fn compressed(bytes: &[u8]) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(bytes)]),
        Alignment::singleton(AlignmentAtom::Compress),
    )
    .expect("canonical OpaqueBytes FAB value")
}

fn assert_stored(state: &ChargedState<Db>, plan: &Plan, key: &[u8; 32], expected: &[u8]) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected native state slots");
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "payloads")
        .expect("payload map declaration");
    let StateValue::Map(payloads) = &*slots.get(slot).expect("payload map state") else {
        panic!("expected OpaqueBytes map");
    };
    let key: AlignedValue = (*key).into();
    let StateValue::Cell(value) = &*payloads.get(&key).expect("stored payload entry") else {
        panic!("expected OpaqueBytes cell");
    };
    assert_eq!(**value, compressed(expected));
}

fn assert_read(execution: &noctium_runtime::Execution, expected: &[u8]) {
    let returns = execution.returns_json();
    assert_eq!(
        returns.get("payload"),
        Some(&json!({"kind":"opaqueBytes", "values":expected}))
    );
    let returns = execution.returns();
    assert_eq!(returns.len(), 1);
    assert_eq!(returns[0].0, "payload");
    assert_eq!(
        returns[0].1.public_json(),
        json!({"kind":"opaqueBytes", "values":expected})
    );

    let mut expected_projection = Vec::new();
    compressed(expected).value_only_field_repr(&mut expected_projection);
    assert_eq!(expected_projection.len(), 1);
    assert_eq!(execution.preimage.public_transcript_outputs.len(), 3);
    assert_eq!(
        &execution.preimage.public_transcript_outputs[2..],
        expected_projection.as_slice()
    );
}

#[test]
#[ignore = "requires fresh Lean artifacts in NOCTIUM_OPAQUE_MAP_DIR"]
fn opaque_bytes_map_round_trips_and_binds_one_compress_field() {
    let artifacts = artifacts();
    let (store_plan, store_circuit) = fixture(&artifacts, "store");
    let (read_plan, read_circuit) = fixture(&artifacts, "read");
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let mut state = create_state(
        &store_plan,
        &BTreeMap::from([("payloads".into(), json!([]))]),
    )
    .expect("empty payload map state creates");

    for (key, payload) in [([0x11; 32], vec![]), ([0x22; 32], vec![0x00, 0x01, 0xff])] {
        let before = state.clone();
        let stored = prepare(
            &store_plan,
            &inputs(&key, Some(&payload)),
            &state,
            params,
            address,
        )
        .expect("canonical payload store prepares");
        check(&stored, &store_circuit).expect("store relation checks");
        assert_eq!(state, before);
        state = stored.after.state;
        assert_stored(&state, &store_plan, &key, &payload);

        let read = prepare(&read_plan, &inputs(&key, None), &state, params, address)
            .expect("stored payload read prepares");
        check(&read, &read_circuit).expect("read relation checks");
        assert_read(&read, &payload);

        let malformed = inputs(&[0x33; 32], Some(&[0x41, 0x00]));
        let unchanged = state.clone();
        assert!(prepare(&store_plan, &malformed, &state, params, address).is_err());
        assert_eq!(state, unchanged);

        if payload == vec![0x00, 0x01, 0xff] {
            let mut altered = read;
            let output_index = altered.preimage.public_transcript_outputs.len() - 1;
            let original_output = altered.preimage.public_transcript_outputs[output_index];
            altered.preimage.public_transcript_outputs[output_index] =
                original_output + Fr::from(1u64);
            assert!(check(&altered, &read_circuit).is_err());
        }
    }
}
