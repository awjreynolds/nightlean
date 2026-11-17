use nightlean_runtime::{
    control::{InvocationTarget, Session, TypedResponse},
    host::{self, Capability, Context, Limits, Operation, Provider},
    witness::{Parameter, WitnessSignature},
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};

#[cfg(feature = "zkir-320")]
const SCALAR_PLAN: &str =
    include_str!("fixtures/witness/320/TypedWitness.ScalarWitness.claim.witness.control.json");
#[cfg(feature = "zkir-320")]
const PAIR_PLAN: &str =
    include_str!("fixtures/witness/320/TypedWitness.PairWitness.claim.witness.control.json");
#[cfg(feature = "zkir-320")]
const UNIT_PLAN: &str =
    include_str!("fixtures/witness/320/TypedWitness.unitRelation.witness.control.json");
#[cfg(feature = "zkir-320")]
const EMPTY_PLAN: &str =
    include_str!("fixtures/witness/320/TypedWitness.emptyRelation.witness.control.json");
#[cfg(feature = "zkir-321")]
const SCALAR_PLAN: &str =
    include_str!("fixtures/witness/321/TypedWitness.ScalarWitness.claim.witness.control.json");
#[cfg(feature = "zkir-321")]
const PAIR_PLAN: &str =
    include_str!("fixtures/witness/321/TypedWitness.PairWitness.claim.witness.control.json");
#[cfg(feature = "zkir-321")]
const UNIT_PLAN: &str =
    include_str!("fixtures/witness/321/TypedWitness.unitRelation.witness.control.json");
#[cfg(feature = "zkir-321")]
const EMPTY_PLAN: &str =
    include_str!("fixtures/witness/321/TypedWitness.emptyRelation.witness.control.json");

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
    let mut operations = BTreeMap::new();
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
        assert!(
            operations
                .insert(
                    signature.operation.clone(),
                    Operation {
                        operation: signature.operation.clone(),
                        argument_schema: arguments,
                        result_schema: signature.result_type.clone(),
                    },
                )
                .is_none()
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
        .or_insert_with(|| ("cache/".into(), BTreeSet::new()));
    assert_eq!(private.0, "cache/");
    private.1.insert(host::STAGE.into());
    let mut capabilities = capability_map
        .into_iter()
        .map(|(id, (key_prefix, operations))| Capability {
            id,
            namespace: "nightlean".into(),
            key_prefix,
            operations: operations.into_iter().collect(),
        })
        .collect::<Vec<_>>();
    capabilities.push(Capability {
        id: "commit".into(),
        namespace: "nightlean".into(),
        key_prefix: "cache/".into(),
        operations: vec![host::CAS.into()],
    });
    Context {
        protocol_version: 1,
        namespace: "nightlean".into(),
        base_revision: "preview-r0".into(),
        attempt_id: attempt_id.into(),
        capabilities,
        operations: operations.into_values().collect(),
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn bound_session(
    plan_text: &str,
    inputs: BTreeMap<String, Json>,
    attempt_id: &str,
) -> (Session, Json) {
    let plan: Json = serde_json::from_str(plan_text).unwrap();
    let digest = hex::encode(Sha256::digest(plan["binding"].as_str().unwrap().as_bytes()));
    let context = source_context(&signatures(&plan), attempt_id);
    let target = binding(&plan)["target"]["entrypoint"]
        .as_str()
        .map(str::to_owned)
        .unwrap_or_else(|| plan["name"].as_str().unwrap().to_owned());
    let session = Session::from_json_with_invocation_target(
        plan.clone(),
        inputs,
        context,
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: target,
        }),
    )
    .unwrap();
    (session, plan)
}

fn binding(plan: &Json) -> Json {
    serde_json::from_str(plan["binding"].as_str().unwrap()).unwrap()
}

fn reply_json(request: &Json, attempt_id: &str, outcome: &str, value: Option<Json>) -> Json {
    let mut response = json!({
        "protocolVersion": 2,
        "requestId": request["requestId"],
        "attemptId": attempt_id,
        "outcome": outcome,
        "operation": request["operation"],
        "capability": request["capability"],
        "schema": request["schema"],
    });
    if outcome == "value" {
        response["value"] = value.unwrap();
    } else {
        response["error"] = json!({"code":"provider_failed"});
    }
    response
}

fn reply(request: &Json, attempt_id: &str, outcome: &str, value: Option<Json>) -> TypedResponse {
    serde_json::from_value(reply_json(request, attempt_id, outcome, value)).unwrap()
}

fn scalar_inputs() -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("expected".into(), json!("14")),
        ("seed".into(), json!("7")),
    ])
}

fn respond_scalar(session: &mut Session, request: &Json, attempt_id: &str) {
    let name = request["name"].as_str().unwrap();
    let value = match name {
        "cache" => session.private_request().unwrap()["invocationWrites"]["cache/last"]["value"]
            .as_str()
            .map(str::to_owned)
            .map(Json::String)
            .unwrap_or_else(|| json!("0")),
        "lookup" => json!("14"),
        _ => panic!("unexpected provider name"),
    };
    session
        .resume_typed(reply(request, attempt_id, "value", Some(value)))
        .unwrap();
}

#[test]
fn typed_repeated_calls_bind_exact_relation_inputs_and_transfer_staged_runtime() {
    let attempt = "a".repeat(64);
    let (mut session, plan) = bound_session(SCALAR_PLAN, scalar_inputs(), &attempt);
    assert!(
        session
            .stage(host::Stage {
                abi_version: 2,
                operation: host::STAGE.into(),
                capability: "private".into(),
                key: "cache/forged".into(),
                ty: "UIntRange<256>".into(),
                value: json!("999"),
            })
            .is_err()
    );
    let first = session.advance().unwrap();
    assert_eq!(first["status"], "need_host");
    assert_eq!(first["request"]["protocolVersion"], 2);
    assert!(first["request"]["requestId"].as_str().is_some_and(|id| {
        id.parse::<u64>()
            .is_ok_and(|number| number.to_string() == id)
    }));
    assert_eq!(first["request"]["name"], "cache");
    assert!(first["request"].get("attemptId").is_some());
    assert!(first["request"].to_string().find("cache/last").is_none());
    let private = session.private_request().unwrap();
    assert_eq!(private["arguments"]["key"], "cache/last");
    assert_eq!(private["invocationWrites"]["cache/last"]["value"], "1");
    assert!(private["invocationWrites"].get("cache/forged").is_none());
    let wrong_attempt = reply(
        &first["request"],
        &"b".repeat(64),
        "value",
        Some(json!("0")),
    );
    assert!(session.resume_typed(wrong_attempt).is_err());
    assert_eq!(session.advance().unwrap(), first);
    respond_scalar(&mut session, &first["request"], &attempt);

    let second = session.advance().unwrap();
    assert_eq!(second["request"]["name"], "cache");
    assert_ne!(
        first["request"]["requestId"],
        second["request"]["requestId"]
    );
    assert_eq!(second["request"]["arguments"], json!([]));
    assert_eq!(
        session.private_request().unwrap()["arguments"]["key"],
        "cache/last"
    );
    respond_scalar(&mut session, &second["request"], &attempt);

    let third = session.advance().unwrap();
    assert_eq!(third["request"]["name"], "lookup");
    assert_eq!(
        third["request"]["arguments"],
        json!([{"name":"seed","type":"UIntRange<256>"}])
    );
    assert_eq!(session.private_request().unwrap()["arguments"]["seed"], "7");
    respond_scalar(&mut session, &third["request"], &attempt);

    let mut previous = third;
    for expected_name in ["cache", "lookup"] {
        let next = session.advance().unwrap();
        assert_eq!(next["request"]["name"], expected_name);
        assert!(
            session
                .resume_typed(reply(
                    &previous["request"],
                    &attempt,
                    "value",
                    Some(json!("14"))
                ))
                .is_err()
        );
        assert_eq!(session.advance().unwrap(), next);
        respond_scalar(&mut session, &next["request"], &attempt);
        previous = next;
    }
    let complete = session.advance().unwrap();
    assert_eq!(complete["status"], "completed");
    assert_eq!(complete["result"], "14");

    let relation = binding(&plan)["nativeRelation"].clone();
    let completion = session.private_completion(&relation).unwrap();
    assert_eq!(completion["inputs"]["expected"], "14");
    assert_eq!(completion["inputs"]["seed"], "7");
    assert_eq!(completion["inputs"]["$helper3"], "1");
    assert_eq!(completion["inputs"]["$helper6"], "1");
    assert_eq!(completion["inputs"]["$helper9"], "14");
    assert_eq!(completion["inputs"]["$helper12"], "1");
    assert_eq!(completion["inputs"]["$helper15"], "14");
    assert_eq!(completion["hostWrites"]["cache/last"]["value"], "14");
    let mut crossed = relation.clone();
    crossed["instructions"][0]["op"] = json!("private_input");
    assert!(session.private_completion(&crossed).is_err());

    assert_eq!(completion["target"]["entrypoint"], "claim");
}

#[test]
fn malformed_crossed_reordered_and_provider_failure_responses_keep_or_reject_the_right_state() {
    let attempt = "d".repeat(64);
    let (mut session, _) = bound_session(SCALAR_PLAN, scalar_inputs(), &attempt);
    let first = session.advance().unwrap();
    let mut malformed = reply_json(&first["request"], &attempt, "value", Some(json!("0")));
    malformed["requestId"] = json!("01");
    assert!(
        session
            .resume_typed(serde_json::from_value(malformed).unwrap())
            .is_err()
    );
    let bad_shape = reply(&first["request"], &attempt, "value", Some(json!("00")));
    assert!(session.resume_typed(bad_shape).is_err());
    assert_eq!(session.advance().unwrap(), first);
    respond_scalar(&mut session, &first["request"], &attempt);
    let second = session.advance().unwrap();
    let failed = reply(&second["request"], &attempt, "error", None);
    assert_eq!(session.resume_typed(failed).unwrap()["status"], "failed");
    assert_eq!(session.advance().unwrap()["status"], "failed");
    assert!(session.private_request().is_err());
}

#[test]
fn dishonest_provider_result_fails_independent_source_constraints() {
    let attempt = "e".repeat(64);
    let (mut session, _) = bound_session(SCALAR_PLAN, scalar_inputs(), &attempt);
    let first = session.advance().unwrap();
    respond_scalar(&mut session, &first["request"], &attempt);
    let second = session.advance().unwrap();
    respond_scalar(&mut session, &second["request"], &attempt);
    let third = session.advance().unwrap();
    assert_eq!(third["request"]["name"], "lookup");
    session
        .resume_typed(reply(
            &third["request"],
            &attempt,
            "value",
            Some(json!("0")),
        ))
        .unwrap();
    let fourth = session.advance().unwrap();
    respond_scalar(&mut session, &fourth["request"], &attempt);
    let fifth = session.advance().unwrap();
    respond_scalar(&mut session, &fifth["request"], &attempt);
    assert_eq!(session.advance().unwrap()["status"], "failed");
    assert!(session.private_request().is_err());
}

#[cfg(feature = "zkir-321")]
#[test]
fn readable_private_state_source_binds_callbacks_stages_and_native_constraints() {
    use nightlean_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
    use onchain_runtime::state::StateValue;
    use transient_crypto::{curve::Fr, fab::AlignedValueExt};

    let plan: Json = serde_json::from_str(include_str!(
        "fixtures/private-authoring/321/NoctiumExamples.PrivateStateCounter.advance.witness.control.json"
    ))
    .unwrap();
    let native_plan: Plan = serde_json::from_str(include_str!(
        "fixtures/private-authoring/321/NoctiumExamples.PrivateStateCounter.advance.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!(
            "fixtures/private-authoring/321/NoctiumExamples.PrivateStateCounter.advance.zkir"
        )
        .as_slice(),
    )
    .unwrap();
    let relation = binding(&plan)["nativeRelation"].clone();
    let key = "noctium/NoctiumExamples.Wallet/saved";
    assert_eq!(
        binding(&plan)["ledgerInputs"],
        json!([
            {"name":"current", "type":"UIntRange<256>", "visibility":"public"}
        ])
    );
    for answer in ["2", "3"] {
        let attempt = "7".repeat(64);
        let make_context = || {
            let mut context = source_context(&signatures(&plan), &attempt);
            context
                .capabilities
                .iter_mut()
                .find(|capability| capability.id == "commit")
                .unwrap()
                .key_prefix = "noctium/NoctiumExamples.Wallet/".into();
            context
        };
        let digest = hex::encode(Sha256::digest(plan["binding"].as_str().unwrap().as_bytes()));
        assert!(
            Session::from_json_with_invocation_target(
                plan.clone(),
                BTreeMap::from([
                    ("expected".into(), json!("2")),
                    ("current".into(), json!("1"))
                ]),
                make_context(),
                Some(&digest),
                Some(InvocationTarget {
                    contract_address: "a".repeat(64),
                    entrypoint: "advance".into(),
                }),
            )
            .is_err()
        );
        let mut session = Session::from_json_with_invocation_target(
            plan.clone(),
            BTreeMap::from([("expected".into(), json!("2"))]),
            make_context(),
            Some(&digest),
            Some(InvocationTarget {
                contract_address: "a".repeat(64),
                entrypoint: "advance".into(),
            }),
        )
        .unwrap();
        let read = session.advance().unwrap();
        assert_eq!(read["request"]["operation"], host::READ);
        assert_eq!(session.private_request().unwrap()["arguments"]["key"], key);
        session
            .resume_typed(reply(&read["request"], &attempt, "value", Some(json!("1"))))
            .unwrap();
        let call = session.advance().unwrap();
        assert_eq!(
            session.private_request().unwrap()["arguments"]["previous"],
            "1"
        );
        assert!(
            session
                .resume_typed(reply(
                    &call["request"],
                    &attempt,
                    "value",
                    Some(json!("256"))
                ))
                .is_err()
        );
        assert_eq!(session.advance().unwrap(), call);
        session
            .resume_typed(reply(
                &call["request"],
                &attempt,
                "value",
                Some(json!(answer)),
            ))
            .unwrap();
        let complete = session.advance().unwrap();
        if answer == "3" {
            assert_eq!(complete["status"], "failed");
            assert!(session.private_completion(&relation).is_err());
            continue;
        }
        assert_eq!(complete["status"], "completed", "{complete}");
        assert_eq!(complete["result"], "2");
        let completion = session.private_completion(&relation).unwrap();
        assert!(completion["inputs"].get("current").is_none());
        assert_eq!(completion["hostWrites"][key]["value"], "2");
        let inputs = serde_json::from_value(completion["inputs"].clone()).unwrap();
        let state = create_state(
            &native_plan,
            &BTreeMap::from([(native_plan.state[0].name.clone(), json!("1"))]),
        )
        .unwrap();
        let mut execution = prepare(
            &native_plan,
            &inputs,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        let wrong_state = create_state(
            &native_plan,
            &BTreeMap::from([(native_plan.state[0].name.clone(), json!("7"))]),
        )
        .unwrap();
        if let Ok(wrong) = prepare(
            &native_plan,
            &inputs,
            &wrong_state,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        ) {
            assert!(check(&wrong, &circuit).is_err());
        }
        let StateValue::Array(state) = execution.after.state.get_ref() else {
            panic!("expected public state array")
        };
        let StateValue::Cell(count) = &*state.get(0).unwrap() else {
            panic!("expected public counter cell")
        };
        let mut fields = Vec::new();
        count.value_only_field_repr(&mut fields);
        assert_eq!(fields, vec![Fr::from(2u64)]);
        // Alter the private read after host validation to exercise the native relation alone.
        execution.preimage.private_transcript[0] = Fr::from(9u64);
        assert!(check(&execution, &circuit).is_err());
    }
}

#[test]
fn fixed_composite_arguments_and_results_keep_component_types_and_private_leaves() {
    let attempt = "f".repeat(64);
    let request = json!({
        "kind":"struct",
        "id":"TypedWitness.Pair",
        "fields":[
            {"name":"amount","value":{"kind":"uint","maximum":"255","value":"7"}},
            {"name":"okay","value":{"kind":"bool","value":true}}
        ]
    });
    let inputs = BTreeMap::from([
        ("expected".into(), json!("14")),
        ("request".into(), request.clone()),
    ]);
    let (mut session, plan) = bound_session(PAIR_PLAN, inputs, &attempt);
    let pending = session.advance().unwrap();
    assert_eq!(pending["request"]["name"], "pair");
    assert_eq!(
        pending["request"]["arguments"],
        json!([{"name":"request","type":"Aggregate:t0"}])
    );
    assert_eq!(
        session.private_request().unwrap()["arguments"]["request"],
        request
    );
    let result = json!({
        "kind":"struct",
        "id":"TypedWitness.Pair",
        "fields":[
            {"name":"amount","value":{"kind":"uint","maximum":"255","value":"14"}},
            {"name":"okay","value":{"kind":"bool","value":true}}
        ]
    });
    session
        .resume_typed(reply(&pending["request"], &attempt, "value", Some(result)))
        .unwrap();
    let complete = session.advance().unwrap();
    assert_eq!(complete["status"], "completed");
    assert_eq!(complete["result"]["kind"], "struct");
    let completion = session
        .private_completion(&binding(&plan)["nativeRelation"])
        .unwrap();
    assert_eq!(completion["inputs"]["request.amount"], "7");
    assert_eq!(completion["inputs"]["request.okay"], "1");
    assert_eq!(completion["inputs"]["$helper7"], "14");
    assert_eq!(completion["inputs"]["$helper8"], "1");
    assert_eq!(completion["hostWrites"]["cache/last"]["value"], "14");
}

#[test]
fn same_provider_across_live_sessions_rejects_crossed_replies() {
    let (mut first, _) = bound_session(SCALAR_PLAN, scalar_inputs(), &"1".repeat(64));
    let (mut second, _) = bound_session(
        SCALAR_PLAN,
        BTreeMap::from([
            ("expected".into(), json!("22")),
            ("seed".into(), json!("9")),
        ]),
        &"2".repeat(64),
    );
    let a = first.advance().unwrap();
    let b = second.advance().unwrap();
    assert_eq!(a["request"]["name"], b["request"]["name"]);
    assert_ne!(a["request"]["requestId"], b["request"]["requestId"]);
    assert!(
        second
            .resume_typed(reply(
                &a["request"],
                &"1".repeat(64),
                "value",
                Some(json!("0"))
            ))
            .is_err()
    );
    assert!(
        first
            .resume_typed(reply(
                &b["request"],
                &"2".repeat(64),
                "value",
                Some(json!("0"))
            ))
            .is_err()
    );
    assert_eq!(first.advance().unwrap(), a);
    assert_eq!(second.advance().unwrap(), b);
}

#[test]
fn unit_and_zero_leaf_nominal_calls_have_canonical_values_and_keep_call_records() {
    let attempt = "9".repeat(64);
    let (mut unit, unit_plan) = bound_session(UNIT_PLAN, BTreeMap::new(), &attempt);
    let pending = unit.advance().unwrap();
    assert_eq!(pending["request"]["name"], "unit");
    assert_eq!(pending["request"]["arguments"], json!([]));
    assert!(
        unit.resume_typed(reply(
            &pending["request"],
            &attempt,
            "value",
            Some(Json::Null)
        ))
        .is_err()
    );
    let mut missing = reply_json(
        &pending["request"],
        &attempt,
        "value",
        Some(json!({"kind":"unit"})),
    );
    missing.as_object_mut().unwrap().remove("value");
    assert!(
        unit.resume_typed(serde_json::from_value::<TypedResponse>(missing).unwrap())
            .is_err()
    );
    assert_eq!(unit.advance().unwrap(), pending);
    unit.resume_typed(reply(
        &pending["request"],
        &attempt,
        "value",
        Some(json!({"kind":"unit"})),
    ))
    .unwrap();
    assert_eq!(unit.advance().unwrap()["status"], "completed");
    let relation = binding(&unit_plan)["nativeRelation"].clone();
    assert_eq!(
        unit.private_completion(&relation).unwrap()["inputs"],
        json!({})
    );

    let (mut empty, empty_plan) = bound_session(EMPTY_PLAN, BTreeMap::new(), &attempt);
    let pending = empty.advance().unwrap();
    assert_eq!(pending["request"]["arguments"], json!([]));
    empty
        .resume_typed(reply(
            &pending["request"],
            &attempt,
            "value",
            Some(json!({"kind":"struct","id":"TypedWitness.Empty","fields":[]})),
        ))
        .unwrap();
    assert_eq!(empty.advance().unwrap()["status"], "completed");
    let relation = binding(&empty_plan)["nativeRelation"].clone();
    assert_eq!(
        empty.private_completion(&relation).unwrap()["inputs"],
        json!({})
    );

    let (mut failed, _) = bound_session(UNIT_PLAN, BTreeMap::new(), &attempt);
    let pending = failed.advance().unwrap();
    assert_eq!(
        failed
            .resume_typed(reply(&pending["request"], &attempt, "error", None))
            .unwrap()["status"],
        "failed"
    );
}

#[test]
fn native_typed_plans_require_a_frozen_matching_target_before_execution() {
    let plan: Json = serde_json::from_str(SCALAR_PLAN).unwrap();
    let digest = hex::encode(Sha256::digest(plan["binding"].as_str().unwrap().as_bytes()));
    let attempt = "8".repeat(64);
    let context = source_context(&signatures(&plan), &attempt);
    assert!(
        Session::from_json_with_binding_sha256(
            plan.clone(),
            scalar_inputs(),
            context,
            Some(&digest),
        )
        .is_err()
    );
    let wrong_context = source_context(&signatures(&plan), &attempt);
    assert!(
        Session::from_json_with_invocation_target(
            plan,
            scalar_inputs(),
            wrong_context,
            Some(&digest),
            Some(InvocationTarget {
                contract_address: "a".repeat(64),
                entrypoint: "other".into(),
            }),
        )
        .is_err()
    );
}

#[test]
fn typed_witness_providers_cannot_impersonate_reserved_state_journal_operations() {
    let attempt = "c".repeat(64);
    for operation in [host::STAGE, host::CAS] {
        let mut plan: Json = serde_json::from_str(UNIT_PLAN).unwrap();
        plan["mode"] = json!("host");
        plan["binding"] = Json::Null;
        plan["witnesses"][0]["operation"] = json!(operation);
        let context = source_context(&signatures(&plan), &attempt);
        assert!(Session::from_json(plan, BTreeMap::new(), context).is_err());
    }
}
