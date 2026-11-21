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
use storage::arena::Sp;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

fn artifacts() -> PathBuf {
    PathBuf::from(
        std::env::var_os("NOCTIUM_OPAQUE_STRING_MAP_DIR")
            .expect("set fresh OpaqueStringMap outputs in NOCTIUM_OPAQUE_STRING_MAP_DIR"),
    )
}

fn fixture(directory: &Path, entry: &str) -> (Plan, IrSource) {
    let stem = format!("OpaqueStringMap.{entry}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit =
        IrSource::load(File::open(directory.join(format!("{stem}.zkir"))).unwrap()).unwrap();
    (plan, circuit)
}

fn input_map(key: &[u8; 32], value: Option<&str>) -> BTreeMap<String, Json> {
    let mut values = BTreeMap::from([(
        "key".into(),
        json!({"kind":"bytes", "values":key.as_slice()}),
    )]);
    if let Some(value) = value {
        values.insert(
            "value".into(),
            json!({"kind":"opaqueString", "value":value}),
        );
    }
    values
}

fn compressed(text: &str) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(text.as_bytes())]),
        Alignment::singleton(AlignmentAtom::Compress),
    )
    .expect("canonical OpaqueString FAB value")
}

fn assert_stored(state: &ChargedState<Db>, plan: &Plan, key: &[u8; 32], expected: &str) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected native state slots");
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "strings")
        .expect("string map declaration");
    let StateValue::Map(strings) = &*slots.get(slot).expect("string map state") else {
        panic!("expected OpaqueString map");
    };
    let key: AlignedValue = (*key).into();
    let StateValue::Cell(value) = &*strings.get(&key).expect("stored string entry") else {
        panic!("expected OpaqueString cell");
    };
    assert_eq!(**value, compressed(expected));
}

fn assert_read(execution: &noctium_runtime::Execution, expected: &str) {
    let expected_json = json!({"kind":"opaqueString", "value":expected});
    assert_eq!(execution.returns_json().get("value"), Some(&expected_json));
    let returns = execution.returns();
    assert_eq!(returns.len(), 1);
    assert_eq!(returns[0].0, "value");
    assert_eq!(returns[0].1.public_json(), expected_json);

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
#[ignore = "requires fresh Lean artifacts in NOCTIUM_OPAQUE_STRING_MAP_DIR"]
fn opaque_string_map_round_trips_canonical_utf8() {
    let artifacts = artifacts();
    let (store_plan, store_circuit) = fixture(&artifacts, "store");
    let (read_plan, read_circuit) = fixture(&artifacts, "read");
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let mut state = create_state(
        &store_plan,
        &BTreeMap::from([("strings".into(), json!([]))]),
    )
    .expect("empty string map state creates");

    for (key, text) in [([0x11; 32], ""), ([0x22; 32], "é\0λ")] {
        let before = state.clone();
        let stored = prepare(
            &store_plan,
            &input_map(&key, Some(text)),
            &state,
            params,
            address,
        )
        .expect("canonical OpaqueString store prepares");
        check(&stored, &store_circuit).expect("store relation checks");
        assert_eq!(state, before);
        state = stored.after.state;
        assert_stored(&state, &store_plan, &key, text);

        let read = prepare(&read_plan, &input_map(&key, None), &state, params, address)
            .expect("stored OpaqueString read prepares");
        check(&read, &read_circuit).expect("read relation checks");
        assert_read(&read, text);

        let unchanged = state.clone();
        let wrong_tag = BTreeMap::from([
            (
                "key".into(),
                json!({"kind":"bytes", "values":vec![0x33u8;32]}),
            ),
            (
                "value".into(),
                json!({"kind":"opaqueBytes", "values":[0x41u8]}),
            ),
        ]);
        assert!(prepare(&store_plan, &wrong_tag, &state, params, address).is_err());
        assert_eq!(state, unchanged);

        let trailing_nul = input_map(&[0x44; 32], Some("é\0"));
        assert!(prepare(&store_plan, &trailing_nul, &state, params, address).is_err());
        assert_eq!(state, unchanged);

        if !text.is_empty() {
            let mut altered = read;
            let output_index = altered.preimage.public_transcript_outputs.len() - 1;
            altered.preimage.public_transcript_outputs[output_index] =
                altered.preimage.public_transcript_outputs[output_index] + Fr::from(1u64);
            assert!(check(&altered, &read_circuit).is_err());
        }
    }

    let invalid_key = [0x55; 32];
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected native state slots");
    };
    let slot = store_plan
        .state
        .iter()
        .position(|declaration| declaration.name == "strings")
        .expect("string map declaration");
    let StateValue::Map(strings) = &*slots.get(slot).expect("string map state") else {
        panic!("expected OpaqueString map");
    };
    let key: AlignedValue = invalid_key.into();
    let invalid_utf8 = AlignedValue::new(
        FabValue(vec![ValueAtom(vec![0xff])]),
        Alignment::singleton(AlignmentAtom::Compress),
    )
    .expect("nonzero byte is a canonical Compress atom");
    let invalid_map = StateValue::Map(strings.insert(key, StateValue::Cell(Sp::new(invalid_utf8))));
    let invalid_state = ChargedState::new(StateValue::Array(
        slots
            .insert(slot, invalid_map)
            .expect("string map slot exists"),
    ));
    let before = invalid_state.clone();
    let error = prepare(
        &read_plan,
        &input_map(&invalid_key, None),
        &invalid_state,
        params,
        address,
    )
    .err()
    .expect("malformed Compress atom is not valid UTF-8");
    assert!(format!("{error:#}").to_lowercase().contains("utf-8"));
    assert_eq!(invalid_state, before);
}
