#![cfg(feature = "zkir-321")]

use noctium_runtime::foreign::{
    ForeignBinaryOp, ForeignFamily, ForeignRole, ForeignType, ForeignValue,
};
use noctium_runtime::{
    Plan, Value, check,
    control::{InvocationTarget, Session, TypedResponse},
    create_state,
    host::{self, Capability, Context, Limits, Operation, Provider},
    prepare,
    zkir::IrSource,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    path::PathBuf,
};

#[test]
#[ignore = "requires fresh Curve25519Witness Lean artifacts via NOCTIUM_CURVE25519_WITNESS_ARTIFACTS"]
fn typed_curve25519_witnesses_feed_the_native_relation() {
    let root = PathBuf::from(
        std::env::var_os("NOCTIUM_CURVE25519_WITNESS_ARTIFACTS")
            .expect("NOCTIUM_CURVE25519_WITNESS_ARTIFACTS"),
    );
    let stem = "Curve25519Witness.claim";
    let source = fs::read_to_string(root.join(format!("{stem}.witness.control.json"))).unwrap();
    let plan: Json = serde_json::from_str(&source).unwrap();
    let native_plan: Plan =
        serde_json::from_slice(&fs::read(root.join(format!("{stem}.impact.json"))).unwrap())
            .unwrap();
    let relation_bytes = fs::read(root.join(format!("{stem}.zkir"))).unwrap();
    let circuit = IrSource::load(relation_bytes.as_slice()).unwrap();

    let scalar_type = ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Scalar);
    let point_type = ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Point);
    let scalar = |number| {
        let mut bytes = [0; 32];
        bytes[0] = number;
        ForeignValue::from_bytes(scalar_type, &bytes).unwrap()
    };
    let input_scalar = scalar(7);
    let returned_scalar = scalar(9);
    let mut generator_bytes = [0x66; 32];
    generator_bytes[0] = 0x58;
    let input_point = ForeignValue::from_bytes(point_type, &generator_bytes).unwrap();
    let returned_point = input_point
        .binary(ForeignBinaryOp::Add, &input_point)
        .unwrap();
    let expected_scalar = returned_scalar
        .binary(ForeignBinaryOp::Add, &scalar(1))
        .unwrap();
    let expected_point = returned_point
        .binary(ForeignBinaryOp::Add, &returned_point)
        .unwrap();
    let input_scalar_json = Value::Foreign(input_scalar).public_json();
    let input_point_json = Value::Foreign(input_point).public_json();
    let returned_scalar_json = Value::Foreign(returned_scalar).public_json();
    let returned_point_json = Value::Foreign(returned_point).public_json();

    let inputs = plan["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|input| {
            let name = input["name"].as_str().unwrap();
            let value = match name {
                "scalar" => input_scalar_json.clone(),
                "point" => input_point_json.clone(),
                "expectedScalar" => Value::Foreign(expected_scalar.clone()).public_json(),
                "expectedPoint" => Value::Foreign(expected_point.clone()).public_json(),
                other => panic!("unexpected source input {other}"),
            };
            (name.to_owned(), value)
        })
        .collect();
    let attempt = "c".repeat(64);
    let digest = hex::encode(Sha256::digest(plan["binding"].as_str().unwrap().as_bytes()));
    let target = binding(&plan)["target"]["entrypoint"]
        .as_str()
        .unwrap()
        .to_owned();
    let mut session = Session::from_json_with_invocation_target(
        plan.clone(),
        inputs,
        source_context(&plan, &attempt),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: target,
        }),
    )
    .unwrap();

    let mut seen = BTreeSet::new();
    loop {
        let status = session.advance().unwrap();
        if status["status"] == "completed" {
            assert_eq!(
                status["result"],
                json!({
                    "kind":"struct",
                    "id":"curve25519WitnessCheck.Output",
                    "fields":[
                        {"name":"scalarMatches","value":{"kind":"bool","value":true}},
                        {"name":"pointMatches","value":{"kind":"bool","value":true}},
                    ],
                })
            );
            break;
        }
        assert_eq!(status["status"], "need_host", "{status}");
        let request = &status["request"];
        let private = session.private_request().unwrap();
        let value = match request["schema"].as_str().unwrap() {
            "Curve25519Scalar" => {
                seen.insert("Curve25519Scalar");
                assert_eq!(private["arguments"]["value"], input_scalar_json);
                returned_scalar_json.clone()
            }
            "Curve25519Point" => {
                seen.insert("Curve25519Point");
                assert_eq!(private["arguments"]["value"], input_point_json);
                // Reuse the codec test's canonical order-two point rejection vector.
                let mut torsion = [0xff; 32];
                torsion[0] = 0xec;
                torsion[31] = 0x7f;
                let invalid = json!({
                    "kind":"foreign",
                    "type":"Curve25519Point",
                    "bytes":torsion,
                });
                assert!(
                    session
                        .resume_typed(reply(request, &attempt, invalid))
                        .is_err()
                );
                returned_point_json.clone()
            }
            other => panic!("unexpected callback result type {other}"),
        };
        session
            .resume_typed(reply(request, &attempt, value))
            .unwrap();
    }
    assert_eq!(
        seen,
        BTreeSet::from(["Curve25519Scalar", "Curve25519Point"])
    );

    let relation = binding(&plan)["nativeRelation"].clone();
    let completion = session.private_completion(&relation).unwrap();
    let native_inputs = completion["inputs"]
        .as_object()
        .unwrap()
        .iter()
        .map(|(name, value)| (name.clone(), value.clone()))
        .collect();
    let state = create_state(&native_plan, &BTreeMap::new()).unwrap();
    let execution = prepare(
        &native_plan,
        &native_inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).unwrap();
}

fn source_context(plan: &Json, attempt_id: &str) -> Context {
    let mut operations = Vec::new();
    let mut providers = Vec::new();
    let mut capabilities = Vec::new();
    for witness in plan["witnesses"].as_array().unwrap() {
        let name = witness["name"].as_str().unwrap().to_owned();
        let operation = witness["operation"].as_str().unwrap().to_owned();
        let capability = witness["capability"].as_str().unwrap().to_owned();
        let arguments = witness["parameters"]
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
        operations.push(Operation {
            operation: operation.clone(),
            argument_schema: arguments,
            result_schema: witness["resultType"].as_str().unwrap().to_owned(),
        });
        providers.push(Provider {
            input: name,
            operation: operation.clone(),
            capability: capability.clone(),
            arguments: BTreeMap::new(),
        });
        capabilities.push(Capability {
            id: capability,
            namespace: "noctium".into(),
            key_prefix: "lookup/".into(),
            operations: vec![operation],
        });
    }
    capabilities.push(Capability {
        id: "private".into(),
        namespace: "noctium".into(),
        key_prefix: "cache/".into(),
        operations: vec![host::STAGE.into()],
    });
    capabilities.push(Capability {
        id: "commit".into(),
        namespace: "noctium".into(),
        key_prefix: "cache/".into(),
        operations: vec![host::CAS.into()],
    });
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "preview-r0".into(),
        attempt_id: attempt_id.into(),
        capabilities,
        operations,
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn binding(plan: &Json) -> Json {
    serde_json::from_str(plan["binding"].as_str().unwrap()).unwrap()
}

fn reply(request: &Json, attempt_id: &str, value: Json) -> TypedResponse {
    serde_json::from_value(json!({
        "protocolVersion":2,
        "requestId":request["requestId"],
        "attemptId":attempt_id,
        "outcome":"value",
        "operation":request["operation"],
        "capability":request["capability"],
        "schema":request["schema"],
        "value":value,
    }))
    .unwrap()
}
