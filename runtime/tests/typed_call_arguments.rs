#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Plan, check, create_state, field_value,
    foreign::{ForeignType, ForeignValue},
    prepare,
    zkir::IrSource,
};
use onchain_runtime::communication_commitment;
use serde_json::json;
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

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
    let execution = prepare(
        &plan,
        &BTreeMap::from([
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
        ]),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        Default::default(),
    )
    .unwrap();
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
}
