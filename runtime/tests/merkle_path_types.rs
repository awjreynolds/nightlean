#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Plan, check,
    control::{InvocationTarget, Session, TypedResponse},
    create_state,
    host::{self, Capability, Context, Limits, Operation, Provider},
    prepare,
    zkir::IrSource,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, env, fs, path::PathBuf};

const EXPECTED_ROOT: &str =
    "23615363679718302500648733510038242834016166715802047945282536128750549339216";

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_MERKLE_PATH_TYPES_DIR")
        .map(PathBuf::from)
        .expect("set fresh outputs in NOCTIUM_MERKLE_PATH_TYPES_DIR")
}

fn context(control: &Json, attempt_id: &str) -> Context {
    let signature = &control["witnesses"][0];
    let name = signature["name"].as_str().unwrap().to_owned();
    let operation = signature["operation"].as_str().unwrap().to_owned();
    let capability = signature["capability"].as_str().unwrap().to_owned();
    let arguments = signature["parameters"]
        .as_array()
        .unwrap()
        .iter()
        .map(|parameter| {
            (
                parameter["name"].as_str().unwrap().to_owned(),
                parameter["type"].as_str().unwrap().to_owned(),
            )
        })
        .collect();
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "merkle-path-types-test".into(),
        attempt_id: attempt_id.into(),
        capabilities: vec![
            Capability {
                id: capability.clone(),
                namespace: "noctium".into(),
                key_prefix: "lookup/".into(),
                operations: vec![operation.clone()],
            },
            Capability {
                id: "private".into(),
                namespace: "noctium".into(),
                key_prefix: "cache/".into(),
                operations: vec![host::STAGE.into()],
            },
            Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "cache/".into(),
                operations: vec![host::CAS.into()],
            },
        ],
        operations: vec![Operation {
            operation: operation.clone(),
            argument_schema: arguments,
            result_schema: signature["resultType"].as_str().unwrap().into(),
        }],
        providers: vec![Provider {
            input: name,
            operation,
            capability,
            arguments: BTreeMap::new(),
        }],
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn session(control: &Json, attempt_id: &str) -> Session {
    let binding_text = control["binding"].as_str().unwrap();
    let binding: Json = serde_json::from_str(binding_text).unwrap();
    let digest = hex::encode(Sha256::digest(binding_text.as_bytes()));
    Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::new(),
        context(control, attempt_id),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: binding["target"]["entrypoint"].as_str().unwrap().into(),
        }),
    )
    .unwrap()
}

fn reply(request: &Json, attempt_id: &str, value: Json) -> TypedResponse {
    serde_json::from_value(json!({
        "protocolVersion": 2,
        "requestId": request["requestId"],
        "attemptId": attempt_id,
        "outcome": "value",
        "operation": request["operation"],
        "capability": request["capability"],
        "schema": request["schema"],
        "value": value,
    }))
    .unwrap()
}

fn path_payload(direction: Option<Json>, depth: usize) -> Json {
    let siblings = [17u64, 29];
    let directions = [json!(true), json!(false)];
    let entries = (0..depth)
        .map(|index| {
            json!({
                "kind":"struct", "id":"MerkleTreePathEntry", "fields":[
                    {"name":"sibling","value":{"kind":"struct","id":"MerkleTreeDigest","fields":[
                        {"name":"field","value":{"kind":"native","value":siblings[index].to_string()}}
                    ]}},
                    {"name":"goes_left","value":{
                        "kind":"bool", "value":direction.clone().unwrap_or_else(|| directions[index].clone())
                    }}
                ]
            })
        })
        .collect::<Vec<_>>();
    json!({
        "kind":"struct", "id":"MerklePathRootNoLeafHash.Path", "fields":[
            {"name":"leaf","value":{"kind":"bytes","values":(1u8..=32).collect::<Vec<_>>()}},
            {"name":"path","value":{"kind":"vector","items":entries}}
        ]
    })
}

fn reject_provider_payload(control: &Json, value: Json) {
    let attempt_id = "b".repeat(64);
    let mut session = session(control, &attempt_id);
    let pending = session.advance().unwrap();
    assert_eq!(pending["status"], "need_host");
    assert!(
        session
            .resume_typed(reply(&pending["request"], &attempt_id, value))
            .is_err()
    );
}

#[test]
#[ignore = "requires fresh MerklePathRootNoLeafHash outputs in NOCTIUM_MERKLE_PATH_TYPES_DIR"]
fn nested_merkle_path_preserves_entry_order_and_checks_provider_shape() {
    let directory = artifacts();
    let stem = "MerklePathRootNoLeafHashSource.digest";
    let control: Json = serde_json::from_slice(
        &fs::read(directory.join(format!("{stem}.witness.control.json"))).unwrap(),
    )
    .unwrap();
    let plan: Plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json"))).unwrap())
            .unwrap();
    let relation = IrSource::load(
        fs::read(directory.join(format!("{stem}.zkir")))
            .unwrap()
            .as_slice(),
    )
    .unwrap();

    let attempt_id = "a".repeat(64);
    let mut session = session(&control, &attempt_id);
    let pending = session.advance().unwrap();
    assert_eq!(pending["status"], "need_host");
    session
        .resume_typed(reply(
            &pending["request"],
            &attempt_id,
            path_payload(None, 2),
        ))
        .unwrap();
    assert_eq!(session.advance().unwrap()["status"], "completed");

    let binding: Json = serde_json::from_str(control["binding"].as_str().unwrap()).unwrap();
    let completion = session
        .private_completion(&binding["nativeRelation"])
        .unwrap();
    let inputs = serde_json::from_value(completion["inputs"].clone()).unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    assert_eq!(
        check(&execution, &relation).unwrap(),
        execution.activity_schedule
    );
    assert_eq!(execution.returns_json()["root"], EXPECTED_ROOT);

    reject_provider_payload(&control, path_payload(Some(json!(2)), 2));
    reject_provider_payload(&control, path_payload(None, 1));
}
