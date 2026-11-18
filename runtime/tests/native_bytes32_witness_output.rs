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
    for grouped in [false, true] {
        let control_text = if grouped {
            include_str!(
                "fixtures/native-grouped-bytes32-witness-output/321/NativeGroupedBytes32WitnessOutput.register.witness.control.json"
            )
        } else {
            include_str!(
                "fixtures/native-bytes32-witness-output/321/NativeBytes32WitnessOutput.register.witness.control.json"
            )
        };
        let plan_text = if grouped {
            include_str!(
                "fixtures/native-grouped-bytes32-witness-output/321/NativeGroupedBytes32WitnessOutput.register.impact.json"
            )
        } else {
            include_str!(
                "fixtures/native-bytes32-witness-output/321/NativeBytes32WitnessOutput.register.impact.json"
            )
        };
        let circuit_bytes: &[u8] = if grouped {
            include_bytes!(
                "fixtures/native-grouped-bytes32-witness-output/321/NativeGroupedBytes32WitnessOutput.register.zkir"
            )
        } else {
            include_bytes!(
                "fixtures/native-bytes32-witness-output/321/NativeBytes32WitnessOutput.register.zkir"
            )
        };
        let control: Json = serde_json::from_str(control_text).unwrap();
        let plan: Plan = serde_json::from_str(plan_text).unwrap();
        let circuit = IrSource::load(circuit_bytes).unwrap();
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
        let mut source_inputs = BTreeMap::from([
            ("accountSecret".into(), bytes(&secret)),
            ("expectedAccountId".into(), bytes(&digest)),
        ]);
        if grouped {
            source_inputs.insert("count".into(), json!("37"));
            assert_eq!(binding["circuitOutputs"].as_array().unwrap().len(), 33);
        }
        let mut session = Session::from_json_with_invocation_target(
            control.clone(),
            source_inputs,
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
        let initial =
            create_state(&plan, &BTreeMap::from([("registered".into(), json!([]))])).unwrap();
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
        if grouped {
            let stored = registered.get(&key).unwrap();
            let StateValue::Cell(value) = &*stored else {
                panic!("expected stored count")
            };
            assert_eq!(
                &**value,
                &noctium_runtime::field_value(transient_crypto::curve::Fr::from(37))
            );
        }

        // The last digest byte is outside the low 248-bit chunk and must still bind.
        let mut changed_digest = digest;
        changed_digest[31] ^= 1;
        let changed_key: AlignedValue = changed_digest.into();
        assert!(registered.get(&changed_key).is_none());
        let mut changed_inputs = inputs;
        changed_inputs.insert("expectedAccountId".into(), bytes(&changed_digest));
        match prepare(&plan, &changed_inputs, &initial, params, address) {
            Err(error) => assert!(error.to_string().contains("helper assertion failed")),
            Ok(changed) => assert!(
                check(&changed, &circuit).is_err(),
                "changed high byte must fail the native helper relation"
            ),
        }
    }
}
