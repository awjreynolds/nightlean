#![cfg(feature = "zkir-321")]

use base_crypto::{fab::AlignedValue, hash::HashOutput};
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan,
    assembly::{CheckedNativeCall, assemble_checked_calls},
    check, create_state, field_value,
    foreign::{ForeignType, ForeignValue},
    prepare,
    zkir::IrSource,
};
use onchain_runtime::{communication_commitment, context::QueryContext, state::EntryPointBuf};
use rand::rngs::OsRng;
use serde_json::json;
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

use ledger::structure::INITIAL_PARAMETERS;

#[test]
fn typed_arguments_use_committed_field_order_without_private_transcript_duplication() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/typed-call-arguments/321/TypedCallArguments.store.impact.json"
    ))
    .unwrap();
    let bytes = include_bytes!("fixtures/typed-call-arguments/321/TypedCallArguments.store.zkir");
    let circuit = IrSource::load(bytes.as_slice()).unwrap();
    let state = |value: &str| {
        create_state(&plan, &BTreeMap::from([("stored".into(), json!(value))])).unwrap()
    };
    let mut field_bytes = [0; 32];
    field_bytes[0] = 9;
    let payload = (0..33).collect::<Vec<u8>>();
    let initial = state("1");
    let inputs = BTreeMap::from([
        ("flag".into(), json!(true)),
        ("score".into(), json!("200")),
        ("payload".into(), json!({"kind":"bytes", "values":payload})),
        ("empty".into(), json!({"kind":"bytes", "values":[]})),
        ("aux".into(), json!("7")),
        ("scalar".into(), json!({"kind":"jubjubScalar", "value":"1"})),
        (
            "point".into(),
            json!({"kind":"jubjubPoint", "x":"0", "y":"1"}),
        ),
        (
            "field".into(),
            json!({"kind":"foreign", "type":"Secp256k1Base", "bytes":field_bytes}),
        ),
    ]);
    let callee = ContractAddress(HashOutput([9; 32]));
    let execution = prepare(&plan, &inputs, &initial, &INITIAL_PARAMETERS, callee).unwrap();
    check(&execution, &circuit).unwrap();
    assert_eq!(execution.after.state, state("200"));
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("tail".into(), json!("32")),
            ("result".into(), json!("200")),
            ("approved".into(), json!(true)),
        ])
    );

    let mut low = [0u8; 32];
    low[..31].copy_from_slice(&payload[..31]);
    let mut raw = vec![
        Fr::from(1u64),
        Fr::from(31u64 + 32 * 256),
        Fr::from_le_bytes(&low).unwrap(),
        Fr::from(200u64),
        Fr::from(0u64),
        Fr::from(1u64),
        Fr::from(1u64),
    ];
    let field_type = ForeignType::parse_source_name("Secp256k1Base").unwrap();
    raw.extend(
        ForeignValue::from_bytes(field_type, &field_bytes)
            .unwrap()
            .encode()
            .unwrap(),
    );
    assert_eq!(execution.preimage.inputs, raw);
    assert_eq!(execution.preimage.private_transcript, [Fr::from(7u64)]);

    let mut altered_header: serde_json::Value = serde_json::from_slice(bytes).unwrap();
    altered_header["inputs"].as_array_mut().unwrap().swap(0, 1);
    let altered_header =
        IrSource::load(serde_json::to_vec(&altered_header).unwrap().as_slice()).unwrap();
    assert!(check(&execution, &altered_header).is_err());

    let mut forged = execution.preimage.clone();
    // The leading high chunk occupies exactly two bytes for Bytes33.
    forged.inputs[1] = forged.inputs[1] + Fr::from(1u64 << 16);
    let aligned = |fields: &[Fr]| {
        AlignedValue::concat(
            fields
                .iter()
                .copied()
                .map(field_value)
                .collect::<Vec<_>>()
                .iter(),
        )
    };
    let changed_input = aligned(&forged.inputs);
    let output = aligned(&[Fr::from(32u64), Fr::from(200u64), Fr::from(1u64)]);
    let randomness = Fr::from(1u64);
    forged.communications_commitment = Some((
        communication_commitment(changed_input, output, randomness),
        randomness,
    ));
    assert!(forged.check(&circuit).is_err());
    let caller_bytes = include_bytes!("fixtures/typed-call-arguments/321/TypedCaller.claim.zkir");
    let caller_circuit = IrSource::load(caller_bytes.as_slice()).unwrap();
    let caller_plan: Plan = serde_json::from_str(include_str!(
        "fixtures/typed-call-arguments/321/TypedCaller.claim.impact.json"
    ))
    .unwrap();
    let caller_state = create_state(
        &caller_plan,
        &BTreeMap::from([("marker".into(), json!("2"))]),
    )
    .unwrap();
    let caller = ContractAddress(HashOutput([8; 32]));
    let callee_entry = EntryPointBuf(b"store".to_vec());
    let mut inputs = inputs;
    inputs.remove("aux");
    inputs.extend([
        (
            "target".into(),
            json!({"kind":"bytes", "values":callee.0.0}),
        ),
        (
            "entryHash".into(),
            json!({"kind":"bytes", "values":callee_entry.ep_hash().0}),
        ),
        ("opening".into(), json!("101")),
        ("emptyAccepted".into(), json!(true)),
        ("expectedTail".into(), json!("32")),
        ("expectedScore".into(), json!("200")),
        ("expectedApproval".into(), json!(true)),
    ]);
    let prepare_caller = |inputs: &BTreeMap<String, serde_json::Value>| {
        prepare(
            &caller_plan,
            inputs,
            &caller_state,
            &INITIAL_PARAMETERS,
            caller,
        )
    };
    let assemble = |source: &noctium_runtime::Execution| {
        assemble_checked_calls(
            &[
                CheckedNativeCall {
                    execution: source,
                    circuit: &caller_circuit,
                    initial_context: QueryContext::new(caller_state.clone(), caller),
                    entry_point: EntryPointBuf(b"claim".to_vec()),
                    communication_commitment_rand: Fr::from(53u64),
                },
                CheckedNativeCall {
                    execution: &execution,
                    circuit: &circuit,
                    initial_context: QueryContext::new(initial.clone(), callee),
                    entry_point: callee_entry.clone(),
                    communication_commitment_rand: Fr::from(101u64),
                },
            ],
            &INITIAL_PARAMETERS,
            1_800_000_000,
            &mut OsRng,
        )
    };

    let source = prepare_caller(&inputs).unwrap();
    let intent = assemble(&source).unwrap();
    let mut calls = intent.calls();
    let parent = calls.next().unwrap();
    let child = calls.next().unwrap();
    assert!(parent.calls(child));
    assert_eq!(child.address, callee);

    inputs.insert("expectedScore".into(), json!("201"));
    let mismatch = prepare_caller(&inputs).unwrap();
    check(&mismatch, &caller_circuit).unwrap();
    assert!(assemble(&mismatch).is_err());

    inputs.insert("emptyAccepted".into(), json!(false));
    assert!(
        prepare_caller(&inputs).is_err(),
        "Bytes0 still evaluates its assertion"
    );
}
