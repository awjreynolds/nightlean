use super::ledger_tests::{advance_native, complete_native_inputs, source_execution};
use super::*;
use crate::control::AuthenticatedNativeTarget;
use crate::{Plan, create_state};
use serde_json::json;

const PLAN: &str =
    include_str!("../../tests/fixtures/iteration-witness/321/IterationWitness.update.impact.json");
const CIRCUIT: &[u8] =
    include_bytes!("../../tests/fixtures/iteration-witness/321/IterationWitness.update.zkir");
const CONTROL: &[u8] = include_bytes!(
    "../../tests/fixtures/iteration-witness/321/IterationWitness.update.witness.control.json"
);
const BINDING: &[u8] = include_bytes!(
    "../../tests/fixtures/iteration-witness/321/IterationWitness.update.witness.json"
);

fn iteration_host_context(control: &Json, attempt: &str) -> Json {
    let mut capabilities = vec![
        json!({"id":"private","namespace":"noctium","keyPrefix":"iteration/","operations":[host::STAGE]}),
        json!({"id":"commit","namespace":"noctium","keyPrefix":"iteration/","operations":[host::CAS]}),
    ];
    let mut operations = Vec::new();
    let mut providers = Vec::new();
    for signature in control["witnesses"].as_array().unwrap() {
        let name = signature["name"].as_str().unwrap();
        capabilities.push(json!({
            "id":name,"namespace":"noctium","keyPrefix":"iteration/","operations":[signature["operation"]]
        }));
        let arguments: BTreeMap<String, Json> = signature["parameters"]
            .as_array()
            .unwrap()
            .iter()
            .map(|parameter| {
                (
                    parameter["name"].as_str().unwrap().into(),
                    parameter["type"].clone(),
                )
            })
            .collect();
        operations.push(json!({"operation":signature["operation"],"argumentSchema":arguments,"resultSchema":signature["resultType"]}));
        providers.push(json!({"input":name,"operation":signature["operation"],"capability":name,"arguments":{}}));
    }
    json!({
        "protocolVersion":1,"namespace":"noctium","baseRevision":"r0","attemptId":attempt,
        "capabilities":capabilities,"operations":operations,"providers":providers,"commitCapability":"commit"
    })
}

#[test]
fn map_fold_preserves_capture_sequence_evaluation_and_provider_order() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("total".into(), json!("0"))])).unwrap();
    let mut reordered: Json = serde_json::from_str(PLAN).unwrap();
    reordered["returnViews"][0]["fields"]
        .as_array_mut()
        .unwrap()
        .swap(0, 1);
    assert!(crate::validate_return_views_json(&reordered).is_err());
    let control: Json = serde_json::from_slice(CONTROL).unwrap();
    let binding: Json = serde_json::from_slice(BINDING).unwrap();
    let unit = binding["inputBindings"]
        .as_array()
        .unwrap()
        .iter()
        .find(|input| input["name"] == "rootUnit")
        .unwrap();
    assert_eq!(unit["type"], "Unit");
    assert_eq!(unit["inputs"], json!([]));
    for (enabled, corrupt) in [(true, false), (false, false), (true, true)] {
        let attempt = if corrupt {
            "c"
        } else if enabled {
            "a"
        } else {
            "b"
        }
        .repeat(64);
        let context_json = iteration_host_context(&control, &attempt);
        let context = serde_json::from_value(context_json.clone()).unwrap();
        let expected = if enabled { "22" } else { "0" };
        let claim = if enabled {
            json!({"kind":"enum","id":"Iteration.Claim","variant":"Applied","fields":[
                {"name":"amount","value":{"kind":"uint","maximum":"31","value":expected}}
            ]})
        } else {
            json!({"kind":"enum","id":"Iteration.Claim","variant":"Empty","fields":[]})
        };
        let expected_receipt = json!({"kind":"struct","id":"Iteration.Receipt","fields":[
            {"name":"total","value":{"kind":"native","value":expected}},
            {"name":"flags","value":{"kind":"vector","items":[
                {"kind":"bool","value":true},{"kind":"bool","value":false}
            ]}},
            {"name":"claim","value":claim},
            {"name":"audit","value":{"kind":"tuple","items":[
                {"kind":"bytes","values":[7,9]},{"kind":"unit"}
            ]}},
            {"name":"releasedOffset","value":{"kind":"native","value":"2"}}
        ]});
        let inputs = BTreeMap::from([
            ("enabled".into(), json!(enabled)),
            ("expected".into(), json!(expected)),
            ("offset".into(), json!("2")),
            ("rootUnit".into(), json!({"kind":"unit"})),
        ]);
        if enabled && !corrupt {
            let mut missing = inputs.clone();
            missing.remove("rootUnit");
            let target = AuthenticatedNativeTarget {
                context_id: 1,
                contract_address: "0".repeat(64),
                entrypoint: "update".into(),
                control_plan: control.clone(),
                control_plan_bytes: CONTROL.to_vec(),
                binding_bytes: BINDING.to_vec(),
                relation: serde_json::from_slice(CIRCUIT).unwrap(),
            };
            assert!(
                control::Session::from_authenticated_native_target(
                    CONTROL,
                    missing,
                    serde_json::from_value(context_json).unwrap(),
                    target,
                )
                .is_err()
            );
        }
        let (mut execution, plan, circuit) =
            source_execution(PLAN, CIRCUIT, CONTROL, BINDING, inputs, &initial, context);
        if enabled {
            let values = json!({"kind":"tuple","items":[
                {"kind":"tuple","items":[
                    {"kind":"uint","maximum":"3","value":"1"},
                    {"kind":"native","value":"0"}
                ]},
                {"kind":"tuple","items":[
                    {"kind":"native","value":"1"},
                    {"kind":"uint","maximum":"3","value":"1"}
                ]},
                {"kind":"tuple","items":[
                    {"kind":"uint","maximum":"7","value":"1"},
                    {"kind":"uint","maximum":"3","value":"2"}
                ]}
            ]});
            for (name, arguments, value) in [
                ("touch", json!({}), json!({"kind":"unit"})),
                ("seed", json!({}), json!("0")),
                ("values", json!({}), values),
                (
                    "double",
                    json!({"value":"3"}),
                    json!(if corrupt { "7" } else { "6" }),
                ),
                ("double", json!({"value":"4"}), json!("8")),
                ("double", json!({"value":"5"}), json!("10")),
            ] {
                let status = execution.advance().unwrap();
                assert_eq!(status["status"], "need_host");
                let request = &status["request"];
                assert_eq!(request["name"], name);
                assert_eq!(execution.private_request().unwrap()["arguments"], arguments);
                let response = serde_json::from_value(json!({
                    "protocolVersion":2,"requestId":request["requestId"],"attemptId":attempt,
                    "operation":request["operation"],"capability":request["capability"],"schema":request["schema"],
                    "outcome":"value","value":value
                })).unwrap();
                execution.resume_typed(response).unwrap();
            }
        }
        if corrupt {
            assert_eq!(execution.advance().unwrap()["status"], "failed");
            continue;
        }
        let result = execution.advance().unwrap();
        assert_eq!(result["status"], "completed");
        assert_eq!(result["result"], expected_receipt);
        let session = execution.session.as_mut().unwrap();
        let relation = serde_json::from_slice(CIRCUIT).unwrap();
        let completion = session.private_completion(&relation).unwrap();
        if enabled {
            assert_eq!(completion["hostWrites"]["iteration/last"]["value"], "22");
        } else {
            assert_eq!(completion["hostWrites"], json!({}));
        }
        let inputs = complete_native_inputs(session, &relation);
        let native = advance_native(&plan, &circuit, &initial, &inputs);
        assert_eq!(native.returns().len(), 8);
        assert_eq!(
            native.returns_json(),
            BTreeMap::from([("result".into(), expected_receipt)])
        );
        assert_eq!(
            native.after.state,
            create_state(&plan, &BTreeMap::from([("total".into(), json!(expected))])).unwrap()
        );
    }
}

#[test]
#[ignore = "requires fresh EmptyTupleIteration artifacts via NOCTIUM_EMPTY_TUPLE_ARTIFACTS"]
fn empty_tuple_iteration_evaluates_arguments_without_invoking_operators() {
    let artifacts =
        std::path::PathBuf::from(std::env::var_os("NOCTIUM_EMPTY_TUPLE_ARTIFACTS").unwrap());
    let read = |extension: &str| {
        std::fs::read(artifacts.join(format!("EmptyTupleIteration.update.{extension}"))).unwrap()
    };
    let impact = String::from_utf8(read("impact.json")).unwrap();
    let binding = read("witness.json");
    let control = read("witness.control.json");
    let circuit = read("zkir");
    let plan: Plan = serde_json::from_str(&impact).unwrap();
    let state = |total: &str| {
        create_state(&plan, &BTreeMap::from([("total".into(), json!(total))])).unwrap()
    };
    let initial = state("0");
    let attempt = "d".repeat(64);
    let context = serde_json::from_value(iteration_host_context(
        &serde_json::from_slice(&control).unwrap(),
        &attempt,
    ))
    .unwrap();
    let (mut execution, plan, relation) = source_execution(
        &impact,
        &circuit,
        &control,
        &binding,
        BTreeMap::new(),
        &initial,
        context,
    );
    for (name, args, value) in [
        ("seed", json!({}), json!("9")),
        (
            "empty",
            json!({"slot":"1"}),
            json!({"kind":"tuple","items":[]}),
        ),
        (
            "empty",
            json!({"slot":"2"}),
            json!({"kind":"tuple","items":[]}),
        ),
        (
            "empty",
            json!({"slot":"3"}),
            json!({"kind":"tuple","items":[]}),
        ),
    ] {
        let step = execution.advance().unwrap();
        assert_eq!(step["status"], "need_host");
        assert_eq!(step["request"]["name"], name);
        assert_eq!(execution.private_request().unwrap()["arguments"], args);
        let request = &step["request"];
        execution.resume_typed(serde_json::from_value(json!({
            "protocolVersion":2,"requestId":request["requestId"],"attemptId":attempt,
            "operation":request["operation"],"capability":request["capability"],"schema":request["schema"],
            "outcome":"value","value":value
        })).unwrap()).unwrap();
    }
    let result = execution.advance().unwrap();
    assert_eq!(result["status"], "completed");
    assert_eq!(result["result"], "9");
    let inputs = complete_native_inputs(
        execution.session.as_mut().unwrap(),
        &serde_json::from_slice(&circuit).unwrap(),
    );
    let native = advance_native(&plan, &relation, &initial, &inputs);
    assert_eq!(
        native.returns_json(),
        BTreeMap::from([("result".into(), json!("9"))])
    );
    assert_eq!(native.after.state, state("9"));
}
