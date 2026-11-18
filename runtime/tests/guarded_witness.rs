#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Plan, check,
    control::{InvocationTarget, Session, TypedResponse},
    create_state, field_decimal,
    host::{self, Capability, Context, Limits, Operation, Provider},
    prepare,
    witness::{Parameter, WitnessSignature},
    zkir::IrSource,
};
use onchain_runtime::state::StateValue;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const SOURCE: &str =
    include_str!("fixtures/guarded-witness/321/GuardedWitness.claim.witness.control.json");
const NATIVE_PLAN: &str =
    include_str!("fixtures/guarded-witness/321/GuardedWitness.claim.impact.json");
const CIRCUIT: &[u8] = include_bytes!("fixtures/guarded-witness/321/GuardedWitness.claim.zkir");

fn signatures(plan: &Json) -> Vec<WitnessSignature> {
    plan["witnesses"]
        .as_array()
        .unwrap()
        .iter()
        .map(|value| WitnessSignature {
            name: value["name"].as_str().unwrap().to_owned(),
            operation: value["operation"].as_str().unwrap().to_owned(),
            capability: value["capability"].as_str().unwrap().to_owned(),
            parameters: value["parameters"]
                .as_array()
                .unwrap()
                .iter()
                .map(|parameter| Parameter {
                    name: parameter["name"].as_str().unwrap().to_owned(),
                    type_token: parameter["type"].as_str().unwrap().to_owned(),
                })
                .collect(),
            result_type: value["resultType"].as_str().unwrap().to_owned(),
            private_key: value["privateKey"].as_str().map(str::to_owned),
        })
        .collect()
}

fn source_context(signatures: &[WitnessSignature], attempt_id: &str) -> Context {
    let mut operations = BTreeMap::<String, Operation>::new();
    let mut providers = Vec::new();
    let mut capability_map = BTreeMap::<String, (String, BTreeSet<String>)>::new();
    for signature in signatures {
        let mut arguments: BTreeMap<_, _> = signature
            .parameters
            .iter()
            .map(|parameter| (parameter.name.clone(), parameter.type_token.clone()))
            .collect();
        if signature.operation == host::READ {
            arguments.insert("key".into(), "Key".into());
        }
        operations.insert(
            signature.operation.clone(),
            Operation {
                operation: signature.operation.clone(),
                argument_schema: arguments,
                result_schema: signature.result_type.clone(),
            },
        );
        let prefix = signature
            .private_key
            .as_deref()
            .map(|key| match key.rsplit_once('/') {
                Some((root, _)) => format!("{root}/"),
                None => key.to_owned(),
            })
            .unwrap_or_else(|| "lookup/".into());
        let entry = capability_map
            .entry(signature.capability.clone())
            .or_insert_with(|| (prefix.clone(), BTreeSet::new()));
        assert_eq!(entry.0, prefix);
        entry.1.insert(signature.operation.clone());
        if signature.private_key.is_some() {
            entry.1.insert(host::STAGE.into());
        }
        providers.push(Provider {
            input: signature.name.clone(),
            operation: signature.operation.clone(),
            capability: signature.capability.clone(),
            arguments: signature
                .private_key
                .as_ref()
                .map(|key| BTreeMap::from([("key".into(), json!(key))]))
                .unwrap_or_default(),
        });
    }
    let private = capability_map
        .entry("private".into())
        .or_insert_with(|| ("guarded/".into(), BTreeSet::new()));
    assert_eq!(private.0, "guarded/");
    private.1.insert(host::STAGE.into());
    let mut capabilities = capability_map
        .into_iter()
        .map(|(id, (key_prefix, operations))| Capability {
            id,
            namespace: "noctium".into(),
            key_prefix,
            operations: operations.into_iter().collect(),
        })
        .collect::<Vec<_>>();
    capabilities.push(Capability {
        id: "commit".into(),
        namespace: "noctium".into(),
        key_prefix: "guarded/".into(),
        operations: vec![host::CAS.into()],
    });
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "preview-r0".into(),
        attempt_id: attempt_id.into(),
        capabilities,
        operations: operations.into_values().collect(),
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

fn bound_session(plan_text: &str, expected: &str, attempt_id: &str) -> (Session, Json) {
    let plan: Json = serde_json::from_str(plan_text).unwrap();
    (session_for_plan(plan.clone(), expected, attempt_id), plan)
}

fn session_for_plan(plan: Json, expected: &str, attempt_id: &str) -> Session {
    let digest = hex::encode(Sha256::digest(plan["binding"].as_str().unwrap().as_bytes()));
    let context = source_context(&signatures(&plan), attempt_id);
    let entrypoint = binding(&plan)["target"]["entrypoint"]
        .as_str()
        .unwrap_or("claim")
        .to_owned();
    Session::from_json_with_invocation_target(
        plan.clone(),
        BTreeMap::from([("expected".into(), json!(expected))]),
        context,
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: entrypoint.into(),
        }),
    )
    .unwrap()
}

fn state_native(state: &onchain_runtime::state::ChargedState<noctium_runtime::Db>) -> String {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let StateValue::Cell(total) = &*slots.get(0).expect("total slot exists") else {
        panic!("expected Native total cell")
    };
    let mut fields = Vec::new();
    total.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

#[test]
fn guarded_branch_binding_checks_selected_providers_and_native_constraints() {
    let native_plan: Plan = serde_json::from_str(NATIVE_PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(
        &native_plan,
        &BTreeMap::from([("total".into(), json!("0"))]),
    )
    .unwrap();
    let plan_json: Json = serde_json::from_str(SOURCE).unwrap();
    let control = binding(&plan_json);
    assert_eq!(control["calls"].as_array().unwrap().len(), 7);
    assert_eq!(
        native_plan
            .circuit
            .inputs
            .iter()
            .filter(|input| input.visibility == "private")
            .count(),
        5
    );

    for (choose, attempt) in [(true, "a".repeat(64)), (false, "b".repeat(64))] {
        let (mut session, plan) = bound_session(SOURCE, "7", &attempt);
        let mut callbacks = Vec::new();
        loop {
            let status = session.advance().unwrap();
            if status["status"] != "need_host" {
                assert_eq!(status["status"], "completed", "{status}");
                assert_eq!(status["result"], "7");
                break;
            }
            let request = &status["request"];
            let name = request["name"].as_str().unwrap();
            callbacks.push(name.to_owned());
            let value = match name {
                "flag" => json!(choose),
                "yesAmount" if choose => json!("7"),
                "unit" if choose => json!({"kind":"unit"}),
                "empty" if !choose => {
                    json!({"kind":"struct","id":"GuardedWitness.Empty","fields":[]})
                }
                "noAmount" if !choose => json!("7"),
                "tail" => {
                    assert_eq!(
                        session.private_request().unwrap()["arguments"]["expected"],
                        "7"
                    );
                    json!("7")
                }
                other => panic!("unexpected provider callback {other} for {choose}"),
            };
            session
                .resume_typed(reply(request, &attempt, value))
                .unwrap();
        }
        let expected_callbacks = if choose {
            vec!["flag", "yesAmount", "unit", "tail"]
        } else {
            vec!["flag", "empty", "noAmount", "tail"]
        };
        assert_eq!(
            callbacks,
            expected_callbacks
                .into_iter()
                .map(str::to_owned)
                .collect::<Vec<_>>()
        );

        let relation = binding(&plan)["nativeRelation"].clone();
        let completion = session.private_completion(&relation).unwrap();
        assert_eq!(completion["hostWrites"]["guarded/last"]["value"], "7");
        let native_inputs: BTreeMap<String, Json> =
            serde_json::from_value(completion["inputs"].clone()).unwrap();
        assert_eq!(native_inputs.len(), native_plan.circuit.inputs.len());
        for input in &native_plan.circuit.inputs {
            assert!(
                native_inputs.contains_key(&input.name),
                "missing {}",
                input.name
            );
        }

        let inactive_name = if choose { "noAmount" } else { "yesAmount" };
        let inactive = control["calls"]
            .as_array()
            .unwrap()
            .iter()
            .find(|call| call["name"] == inactive_name)
            .unwrap()["inputs"][0]
            .as_str()
            .unwrap();
        assert_eq!(native_inputs[inactive], "0", "inactive field {inactive}");

        let mut execution = prepare(
            &native_plan,
            &native_inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        assert_eq!(state_native(&execution.after.state), "7");
        assert_eq!(execution.returns_json()["observed"], "7");

        let private_names: Vec<_> = native_plan
            .circuit
            .inputs
            .iter()
            .filter(|input| input.visibility == "private")
            .map(|input| input.name.as_str())
            .collect();
        let position = private_names
            .iter()
            .position(|name| name == &inactive)
            .unwrap();
        execution.preimage.private_transcript[position] = Fr::from(9u64);
        assert!(check(&execution, &circuit).is_err());
    }
}

#[test]
fn guarded_call_rejects_malformed_guard_before_requesting_a_provider() {
    let attempt = "c".repeat(64);
    for guard in [
        json!({"tag":"constant","value":"1"}),
        json!({"tag":"reference","name":"unavailable"}),
    ] {
        let mut plan: Json = serde_json::from_str(SOURCE).unwrap();
        let mut control = binding(&plan);
        control["calls"][0]["guard"] = guard;
        plan["binding"] = json!(serde_json::to_string(&control).unwrap());
        match Session::from_json_with_invocation_target(
            plan.clone(),
            BTreeMap::from([("expected".into(), json!("7"))]),
            source_context(&signatures(&plan), &attempt),
            Some(&hex::encode(Sha256::digest(
                plan["binding"].as_str().unwrap().as_bytes(),
            ))),
            Some(InvocationTarget {
                contract_address: "a".repeat(64),
                entrypoint: "claim".into(),
            }),
        ) {
            Err(_) => {}
            Ok(mut session) => {
                let status = session.advance();
                assert!(
                    status.is_err()
                        || status
                            .as_ref()
                            .is_ok_and(|status| status["status"] == "failed"),
                    "malformed guard reached a provider: {status:?}"
                );
            }
        }
    }
}
