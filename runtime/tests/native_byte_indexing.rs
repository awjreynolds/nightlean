#![cfg(feature = "zkir-321")]

use nightlean_runtime::{Plan, check, create_state, field_value, prepare, zkir::IrSource};
use onchain_runtime::state::StateValue;
use serde_json::json;
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

#[test]
fn computed_bytes_index_through_hash_serialization_and_selection() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/native-byte-indexing/321/NativeByteIndexing.inspect.impact.json"
    ))
    .unwrap();
    let circuit: &[u8] =
        include_bytes!("fixtures/native-byte-indexing/321/NativeByteIndexing.inspect.zkir");
    let circuit = IrSource::load(circuit).unwrap();
    let names = [
        "rawFirst",
        "digestFirst",
        "digestLast",
        "serializedSecond",
        "selectedByte",
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
        let execution = prepare(
            &plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        let StateValue::Array(state) = execution.after.state.get_ref() else {
            panic!("expected state array")
        };
        let expected = [
            payload[0],
            digest[0],
            digest[31],
            1,
            if choose_hash { digest[7] } else { 0 },
        ];
        for (index, byte) in expected.into_iter().enumerate() {
            let StateValue::Cell(cell) = state.get(index).unwrap() else {
                panic!("expected byte cell")
            };
            assert_eq!(**cell, field_value(Fr::from(byte as u64)));
        }
    }
}
