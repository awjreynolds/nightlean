#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Plan, check,
    control::{InvocationTarget, Session},
    create_state,
    host::{self, Capability, Context, Limits},
    prepare,
    zkir::IrSource,
};
use onchain_runtime::state::StateValue;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;

fn bytes(value: &[u8; 32]) -> Json {
    json!({"kind":"bytes", "values":value.as_slice()})
}

#[test]
fn disclosed_bytes32_helper_result_binds_the_full_native_ledger_key() {
    let control: Json = serde_json::from_str(include_str!(
        "fixtures/native-bytes32-witness-output/321/NativeBytes32WitnessOutput.register.witness.control.json"
    ))
    .unwrap();
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/native-bytes32-witness-output/321/NativeBytes32WitnessOutput.register.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!(
            "fixtures/native-bytes32-witness-output/321/NativeBytes32WitnessOutput.register.zkir"
        )
        .as_slice(),
    )
    .unwrap();
    let secret = [42u8; 32];
    let digest: [u8; 32] = Sha256::digest(secret).into();
    let context = Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "genesis-r0".into(),
        attempt_id: "b".repeat(64),
        capabilities: vec![Capability {
            id: "commit".into(),
            namespace: "noctium".into(),
            key_prefix: "noctium/".into(),
            operations: vec![host::CAS.into()],
        }],
        operations: vec![],
        providers: vec![],
        commit_capability: "commit".into(),
        limits: Limits::default(),
    };
    let binding_text = control["binding"].as_str().unwrap();
    let binding: Json = serde_json::from_str(binding_text).unwrap();
    let binding_digest = hex::encode(Sha256::digest(binding_text.as_bytes()));
    let mut session = Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([
            ("accountSecret".into(), bytes(&secret)),
            ("expectedAccountId".into(), bytes(&digest)),
        ]),
        context,
        Some(&binding_digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: "register".into(),
        }),
    )
    .unwrap();
    assert_eq!(session.advance().unwrap()["status"], "completed");
    let completion = session
        .private_completion(&binding["nativeRelation"])
        .unwrap();
    let inputs: BTreeMap<String, Json> =
        serde_json::from_value(completion["inputs"].clone()).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("registered".into(), json!([]))])).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let execution = prepare(&plan, &inputs, &initial, params, address).unwrap();
    check(&execution, &circuit).unwrap();
    let StateValue::Array(root) = execution.after.state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(registered) = root.get(0).unwrap() else {
        panic!("expected registered map")
    };
    let key: AlignedValue = digest.into();
    assert!(registered.get(&key).is_some());

    // The last digest byte is outside the low 248-bit chunk and must still bind.
    let mut changed_digest = digest;
    changed_digest[31] ^= 1;
    let changed_key: AlignedValue = changed_digest.into();
    assert!(registered.get(&changed_key).is_none());
    let mut changed_inputs = inputs;
    changed_inputs.insert("expectedAccountId".into(), bytes(&changed_digest));
    let error = prepare(&plan, &changed_inputs, &initial, params, address)
        .err()
        .expect("changed high byte must fail the helper equality");
    assert!(error.to_string().contains("helper assertion failed"));
}
