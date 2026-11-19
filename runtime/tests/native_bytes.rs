#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Expr, Plan, ScalarType, Value, check, create_state, field_value, prepare, witness::Registry,
    zkir::IrSource,
};
use onchain_runtime::state::StateValue;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

#[test]
fn general_bytes_preserve_chunk_boundaries_types_and_committed_returns() {
    let (plan, circuit): (Plan, IrSource) = if let Some(output) =
        std::env::var_os("NOCTIUM_NATIVE_BYTES_ARTIFACTS")
    {
        let output = std::path::PathBuf::from(output);
        (
            serde_json::from_slice(
                &std::fs::read(output.join("NativeBytes.inspect.impact.json")).unwrap(),
            )
            .unwrap(),
            IrSource::load(std::fs::File::open(output.join("NativeBytes.inspect.zkir")).unwrap())
                .unwrap(),
        )
    } else {
        (
            serde_json::from_str(include_str!(
                "fixtures/native-bytes/321/NativeBytes.inspect.impact.json"
            ))
            .unwrap(),
            IrSource::load(
                include_bytes!("fixtures/native-bytes/321/NativeBytes.inspect.zkir").as_slice(),
            )
            .unwrap(),
        )
    };
    let names = [
        "payload31",
        "payload32",
        "payload62",
        "payload63",
        "selectedFirst",
        "selectedLast",
        "joined31",
        "joined32",
        "joined62",
        "joined63",
        "sliceFirst",
        "sliceLast",
        "literalLast",
    ];
    let initial = create_state(
        &plan,
        &names
            .iter()
            .map(|name| ((*name).into(), json!("0")))
            .collect(),
    )
    .unwrap();
    let payload: Vec<u8> = (0..64).collect();
    let other: Vec<u8> = (100..131).collect();
    let wide: Vec<u8> = (200..233).collect();
    let joined: Vec<_> = other.iter().chain(&wide).copied().collect();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let mut last_inputs = BTreeMap::new();
    for choose_reverse in [false, true] {
        let inputs = BTreeMap::from([
            ("payload".into(), bytes(&payload)),
            ("other31".into(), bytes(&other)),
            ("wide33".into(), bytes(&wide)),
            ("empty0".into(), bytes(&[])),
            ("chooseReverse".into(), json!(choose_reverse)),
        ]);
        let execution = prepare(&plan, &inputs, &initial, params, address).unwrap();
        check(&execution, &circuit).unwrap();
        let mut selected = payload.clone();
        if choose_reverse {
            selected.reverse();
        }
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([
                ("selectedBytes".into(), bytes(&selected)),
                ("joinedBytes".into(), bytes(&joined)),
                ("sliceBytes".into(), bytes(&payload[31..63])),
                ("otherBytes".into(), bytes(&other)),
                ("wideBytes".into(), bytes(&wide)),
                ("emptyBytes".into(), bytes(&[])),
            ])
        );
        let StateValue::Array(state) = execution.after.state.get_ref() else {
            panic!("expected state array");
        };
        let expected = [
            31,
            32,
            62,
            63,
            selected[0],
            selected[63],
            200,
            201,
            231,
            232,
            31,
            62,
            68,
        ];
        for (index, byte) in expected.into_iter().enumerate() {
            let StateValue::Cell(cell) = state.get(index).unwrap() else {
                panic!("expected byte cell");
            };
            assert_eq!(**cell, field_value(Fr::from(byte as u64)));
        }
        last_inputs = inputs;
    }
    let mut forged = plan.clone();
    let mut changed = payload.clone();
    changed.reverse();
    changed[62] ^= 1;
    forged.returns[0].expression = Expr::BytesLiteral {
        length: 64,
        values: changed,
    };
    let forged = prepare(&forged, &last_inputs, &initial, params, address).unwrap();
    assert!(check(&forged, &circuit).is_err());
    last_inputs.insert("payload".into(), bytes(&payload[..63]));
    assert!(prepare(&plan, &last_inputs, &initial, params, address).is_err());

    let registry = Registry::default();
    for length in [0, 1, 31, 32, 33, 62, 63, 64, 1024] {
        let token = format!("Bytes<{length}>");
        let value = vec![255; length];
        assert_eq!(
            ScalarType::parse(&token).unwrap().bytes_length(),
            Some(length)
        );
        Value::Bytes(value.clone()).validate().unwrap();
        registry.validate(&token, &bytes(&value)).unwrap();
        assert!(
            registry
                .validate(&token, &bytes(&vec![0; length + 1]))
                .is_err()
        );
    }
    assert_eq!(ScalarType::parse("Bytes<32>").unwrap(), ScalarType::Bytes32);
    for token in ["Bytes<1025>", "Bytes<01>", "Bytes<-1>", "Bytes<>"] {
        assert!(ScalarType::parse(token).is_err());
    }
    assert!(Value::Bytes(vec![0; 1025]).validate().is_err());

    let empty_plan: Plan = serde_json::from_str(include_str!(
        "fixtures/native-bytes/321/NativeEmptyBytes.inspect.impact.json"
    ))
    .unwrap();
    let empty_circuit = IrSource::load(
        include_bytes!("fixtures/native-bytes/321/NativeEmptyBytes.inspect.zkir").as_slice(),
    )
    .unwrap();
    let empty_state = create_state(&empty_plan, &BTreeMap::new()).unwrap();
    let mut empty_execution = prepare(
        &empty_plan,
        &BTreeMap::from([
            ("enabled".into(), json!(true)),
            ("empty0".into(), bytes(&[])),
        ]),
        &empty_state,
        params,
        address,
    )
    .unwrap();
    check(&empty_execution, &empty_circuit).unwrap();
    assert_eq!(empty_execution.preimage.private_transcript.len(), 1);
    empty_execution.preimage.private_transcript[0] = Fr::from(0u64);
    assert!(check(&empty_execution, &empty_circuit).is_err());
}
