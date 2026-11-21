#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::context::QueryContext;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

#[test]
#[ignore = "requires fresh NativeTokenColors artifacts in NOCTIUM_NATIVE_TOKEN_COLORS_DIR"]
fn native_token_and_contract_colors_match_compact() {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_NATIVE_TOKEN_COLORS_DIR").expect("NOCTIUM_NATIVE_TOKEN_COLORS_DIR"),
    );
    let plan: Plan = serde_json::from_slice(
        &fs::read(directory.join("NativeTokenColors.derive.impact.json")).unwrap(),
    )
    .unwrap();
    let circuit_bytes = fs::read(directory.join("NativeTokenColors.derive.zkir")).unwrap();
    let circuit = IrSource::load(circuit_bytes.as_slice()).unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let domain: [u8; 32] = std::array::from_fn(|index| (index + 1) as u8);
    let inputs = BTreeMap::<String, Json>::from([("domain".into(), bytes(&domain))]);
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let cases = [
        (
            std::array::from_fn(|index| (index + 1) as u8),
            "f134d9173e664429ea3152bf6097ed6daa96b76357737c1442a008b9ce3e4d3f",
        ),
        (
            [0xa5; 32],
            "91592370010382a8902fc27fa786031af985768817d249f35c77b3678271cd42",
        ),
    ];

    for (address_bytes, expected_color) in cases {
        let address = ContractAddress(HashOutput(address_bytes));
        let context = QueryContext::new(initial.clone(), address);
        let execution = prepare_with_context(&plan, &inputs, context, parameters).unwrap();
        assert_eq!(
            check(&execution, &circuit).unwrap(),
            execution.activity_schedule
        );
        assert_eq!(execution.returns_json()["nativeColor"], bytes(&[0; 32]));
        assert_eq!(
            execution.returns_json()["derivedColor"],
            bytes(&hex::decode(expected_color).unwrap()),
        );
    }
}
