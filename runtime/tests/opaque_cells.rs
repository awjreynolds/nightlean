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
        std::env::var_os("NOCTIUM_OPAQUE_CELLS_DIR")
            .expect("set fresh OpaqueCells outputs in NOCTIUM_OPAQUE_CELLS_DIR"),
    )
}

fn fixture(directory: &Path, entry: &str) -> (Plan, IrSource) {
    let stem = format!("OpaqueCells.{entry}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit =
        IrSource::load(File::open(directory.join(format!("{stem}.zkir"))).unwrap()).unwrap();
    (plan, circuit)
}

fn write_inputs(text: &str, bytes: &[u8]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        (
            "nextText".into(),
            json!({"kind":"opaqueString", "value":text}),
        ),
        (
            "nextBytes".into(),
            json!({"kind":"opaqueBytes", "values":bytes}),
        ),
    ])
}

fn compressed(bytes: &[u8]) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(bytes)]),
        Alignment::singleton(AlignmentAtom::Compress),
    )
    .expect("canonical opaque Compress value")
}

fn assert_cell(state: &ChargedState<Db>, plan: &Plan, name: &str, expected: &[u8]) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected native root state cells");
    };
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == name)
        .expect("opaque cell declaration");
    let StateValue::Cell(value) = &*slots.get(slot).expect("opaque cell slot") else {
        panic!("expected one root Cell");
    };
    assert_eq!(**value, compressed(expected));
}

fn assert_read(
    execution: &noctium_runtime::Execution,
    return_name: &str,
    expected_json: Json,
    expected_bytes: &[u8],
) {
    assert_eq!(
        execution.returns_json().get(return_name),
        Some(&expected_json)
    );
    let returns = execution.returns();
    assert_eq!(returns.len(), 1);
    assert_eq!(returns[0].0, return_name);
    assert_eq!(returns[0].1.public_json(), expected_json);

    let mut expected_projection = Vec::new();
    compressed(expected_bytes).value_only_field_repr(&mut expected_projection);
    assert_eq!(expected_projection.len(), 1);
    assert_eq!(
        execution.preimage.public_transcript_outputs,
        expected_projection
    );
}

#[test]
#[ignore = "requires fresh Lean artifacts in NOCTIUM_OPAQUE_CELLS_DIR"]
fn opaque_root_cells_round_trip_and_bind_compress_values() {
    let artifacts = artifacts();
    let (write_plan, write_circuit) = fixture(&artifacts, "store");
    let (text_plan, text_circuit) = fixture(&artifacts, "readText");
    let (bytes_plan, bytes_circuit) = fixture(&artifacts, "readBytes");
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let state = create_state(
        &write_plan,
        &BTreeMap::from([
            ("text".into(), json!({"kind":"opaqueString", "value":""})),
            ("bytes".into(), json!({"kind":"opaqueBytes", "values":[]})),
        ]),
    )
    .expect("empty opaque root cells create");
    assert_cell(&state, &write_plan, "text", b"");
    assert_cell(&state, &write_plan, "bytes", b"");

    let no_inputs = BTreeMap::new();
    let empty_text = prepare(&text_plan, &no_inputs, &state, parameters, address)
        .expect("empty OpaqueString Cell reads");
    check(&empty_text, &text_circuit).expect("empty string read relation checks");
    assert_read(
        &empty_text,
        "textValue",
        json!({"kind":"opaqueString", "value":""}),
        b"",
    );
    let empty_bytes = prepare(&bytes_plan, &no_inputs, &state, parameters, address)
        .expect("empty OpaqueBytes Cell reads");
    check(&empty_bytes, &bytes_circuit).expect("empty bytes read relation checks");
    assert_read(
        &empty_bytes,
        "bytesValue",
        json!({"kind":"opaqueBytes", "values":[]}),
        b"",
    );

    let text = "é\0λ";
    let bytes = [0x00, 0x01, 0xff];
    let before = state.clone();
    let mut stored = prepare(
        &write_plan,
        &write_inputs(text, &bytes),
        &state,
        parameters,
        address,
    )
    .expect("canonical OpaqueString and OpaqueBytes Cell write prepares");
    check(&stored, &write_circuit).expect("opaque Cell write relation checks");
    assert_eq!(state, before);

    let mut expected_input_projection = Vec::new();
    compressed(text.as_bytes()).value_only_field_repr(&mut expected_input_projection);
    compressed(&bytes).value_only_field_repr(&mut expected_input_projection);
    assert_eq!(expected_input_projection.len(), 2);
    for value in expected_input_projection {
        let input_index = stored
            .preimage
            .public_transcript_inputs
            .iter()
            .position(|field| *field == value)
            .expect("opaque Compress input is present in the public operation transcript");
        let original_input = stored.preimage.public_transcript_inputs[input_index];
        stored.preimage.public_transcript_inputs[input_index] = original_input + Fr::from(1u64);
        assert!(check(&stored, &write_circuit).is_err());
        stored.preimage.public_transcript_inputs[input_index] = original_input;
    }
    let next_state = stored.after.state.clone();
    assert_cell(&next_state, &write_plan, "text", text.as_bytes());
    assert_cell(&next_state, &write_plan, "bytes", &bytes);

    let text_read = prepare(&text_plan, &no_inputs, &next_state, parameters, address)
        .expect("stored OpaqueString Cell reads");
    check(&text_read, &text_circuit).expect("string read relation checks");
    assert_read(
        &text_read,
        "textValue",
        json!({"kind":"opaqueString", "value":text}),
        text.as_bytes(),
    );
    let mut altered_text = text_read;
    let last_text = altered_text
        .preimage
        .public_transcript_outputs
        .last_mut()
        .expect("string Compress proof output");
    *last_text = *last_text + Fr::from(1u64);
    assert!(check(&altered_text, &text_circuit).is_err());

    let bytes_read = prepare(&bytes_plan, &no_inputs, &next_state, parameters, address)
        .expect("stored OpaqueBytes Cell reads");
    check(&bytes_read, &bytes_circuit).expect("bytes read relation checks");
    assert_read(
        &bytes_read,
        "bytesValue",
        json!({"kind":"opaqueBytes", "values":bytes}),
        &bytes,
    );
    let mut altered_bytes = bytes_read;
    let last_bytes = altered_bytes
        .preimage
        .public_transcript_outputs
        .last_mut()
        .expect("bytes Compress proof output");
    *last_bytes = *last_bytes + Fr::from(1u64);
    assert!(check(&altered_bytes, &bytes_circuit).is_err());

    let unchanged = next_state.clone();
    assert!(
        prepare(
            &write_plan,
            &write_inputs("é\0", &bytes),
            &next_state,
            parameters,
            address,
        )
        .is_err()
    );
    assert!(
        prepare(
            &write_plan,
            &write_inputs(text, &[0x41, 0x00]),
            &next_state,
            parameters,
            address,
        )
        .is_err()
    );
    assert_eq!(next_state, unchanged);
}
