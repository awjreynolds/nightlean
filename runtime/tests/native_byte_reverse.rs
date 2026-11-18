#![cfg(feature = "zkir-321")]

use noctium_runtime::{Plan, check, create_state, field_value, prepare, zkir::IrSource};
use onchain_runtime::state::StateValue;
use serde_json::json;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

#[test]
fn reverse_octets_across_raw_hash_serialized_and_selected_bytes() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/native-byte-reverse/321/NativeByteReverse.inspect.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/native-byte-reverse/321/NativeByteReverse.inspect.zkir")
            .as_slice(),
    )
    .unwrap();
    let names = [
        "rawFirst",
        "rawLast",
        "digestFirst",
        "serializedFirst",
        "selectedFirst",
        "roundTripFirst",
    ];
    let initial = create_state(
        &plan,
        &names
            .iter()
            .map(|name| ((*name).into(), json!("0")))
            .collect(),
    )
    .unwrap();
    let payload: [u8; 32] = std::array::from_fn(|index| index as u8 + 1);
    let digest = Sha256::digest(payload);
    for choose_hash in [false, true] {
        let inputs = BTreeMap::from([
            (
                "payload".into(),
                json!({"kind":"bytes","values":payload.as_slice()}),
            ),
            ("field".into(), json!("259")),
            ("chooseHash".into(), json!(choose_hash)),
        ]);
        let mut execution = prepare(
            &plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        let StateValue::Array(state) = execution.after.state.get_ref() else {
            panic!("expected state array");
        };
        let expected = [
            32,
            1,
            digest[31],
            0,
            if choose_hash { digest[31] } else { 0 },
            1,
        ];
        for (index, byte) in expected.into_iter().enumerate() {
            let StateValue::Cell(cell) = state.get(index).unwrap() else {
                panic!("expected byte cell");
            };
            assert_eq!(**cell, field_value(Fr::from(byte as u64)));
        }
        let last = execution
            .preimage
            .public_transcript_inputs
            .last_mut()
            .unwrap();
        *last = *last + Fr::from(1u64);
        assert!(check(&execution, &circuit).is_err());
    }
}
