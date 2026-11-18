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

#[test]
fn map_fold_preserves_capture_sequence_evaluation_and_provider_order() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("total".into(), json!("0"))])).unwrap();
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
        let mut capabilities = vec![
            json!({"id":"private","namespace":"noctium","keyPrefix":"iteration/","operations":[host::STAGE]}),
            json!({"id":"commit","namespace":"noctium","keyPrefix":"iteration/","operations":[host::CAS]}),
        ];
        let mut operations = Vec::new();
        let mut providers = Vec::new();
        for name in ["touch", "seed", "values", "double"] {
            let signature = control["witnesses"]
                .as_array()
                .unwrap()
                .iter()
                .find(|signature| signature["name"] == name)
                .unwrap();
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
        let context_json = json!({
            "protocolVersion":1,"namespace":"noctium","baseRevision":"r0","attemptId":attempt,
            "capabilities":capabilities,"operations":operations,"providers":providers,"commitCapability":"commit"
        });
        let context = serde_json::from_value(context_json.clone()).unwrap();
        let expected = if enabled { "24" } else { "0" };
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
            let values = json!({"kind":"vector","items":[
                {"kind":"native","value":"1"},
                {"kind":"native","value":"2"},
                {"kind":"native","value":"3"}
            ]});
            for (name, arguments, value) in [
                ("touch", json!({}), json!({"kind":"unit"})),
                ("seed", json!({}), json!("0")),
                ("values", json!({}), values),
                ("double", json!({"value":"3"}), json!("6")),
                (
                    "double",
                    json!({"value":"4"}),
                    json!(if corrupt { "9" } else { "8" }),
                ),
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
        assert_eq!(result["result"], expected);
        let session = execution.session.as_mut().unwrap();
        let relation = serde_json::from_slice(CIRCUIT).unwrap();
        let completion = session.private_completion(&relation).unwrap();
        if enabled {
            assert_eq!(completion["hostWrites"]["iteration/last"]["value"], "24");
        } else {
            assert_eq!(completion["hostWrites"], json!({}));
        }
        let inputs = complete_native_inputs(session, &relation);
        let native = advance_native(&plan, &circuit, &initial, &inputs);
        assert_eq!(
            native.returns_json(),
            BTreeMap::from([("result".into(), json!(expected))])
        );
        assert_eq!(
            native.after.state,
            create_state(&plan, &BTreeMap::from([("total".into(), json!(expected))])).unwrap()
        );
    }
}
