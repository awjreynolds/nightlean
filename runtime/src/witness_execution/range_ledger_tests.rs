use super::ledger_tests::{advance_native, complete_native_inputs, source_execution};
use super::*;
use crate::{Plan, create_state};
use serde_json::json;

const PLAN: &str = include_str!(
    "../../tests/fixtures/finite-range-witness/321/FiniteRangeWitness.update.impact.json"
);
const CIRCUIT: &[u8] =
    include_bytes!("../../tests/fixtures/finite-range-witness/321/FiniteRangeWitness.update.zkir");
const CONTROL: &[u8] = include_bytes!(
    "../../tests/fixtures/finite-range-witness/321/FiniteRangeWitness.update.witness.control.json"
);
const BINDING: &[u8] = include_bytes!(
    "../../tests/fixtures/finite-range-witness/321/FiniteRangeWitness.update.witness.json"
);

#[test]
fn finite_range_orders_state_dependent_providers_and_private_stages() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("total".into(), json!("0"))])).unwrap();
    for enabled in [true, false] {
        let attempt = if enabled {
            "a".repeat(64)
        } else {
            "b".repeat(64)
        };
        let context = serde_json::from_value(json!({
            "protocolVersion":1,"namespace":"noctium","baseRevision":"r0","attemptId":attempt,
            "capabilities":[
                {"id":"step","namespace":"noctium","keyPrefix":"loop/","operations":["noctium.range-step.v1"]},
                {"id":"private","namespace":"noctium","keyPrefix":"loop/","operations":[host::STAGE]},
                {"id":"commit","namespace":"noctium","keyPrefix":"loop/","operations":[host::CAS]}
            ],
            "operations":[{"operation":"noctium.range-step.v1","argumentSchema":{"index":"Native","before":"Native"},"resultSchema":"Native"}],
            "providers":[{"input":"step","operation":"noctium.range-step.v1","capability":"step","arguments":{}}],
            "commitCapability":"commit"
        })).unwrap();
        let expected = if enabled { "6" } else { "0" };
        let (mut execution, plan, circuit) = source_execution(
            PLAN,
            CIRCUIT,
            CONTROL,
            BINDING,
            BTreeMap::from([
                ("enabled".into(), json!(enabled)),
                ("expected".into(), json!(expected)),
            ]),
            &initial,
            context,
        );
        if enabled {
            for (index, before) in [(1, 0), (2, 1), (3, 3)] {
                let status = execution.advance().unwrap();
                assert_eq!(status["status"], "need_host");
                let request = &status["request"];
                assert_eq!(request["name"], "step");
                let private = execution.private_request().unwrap();
                assert_eq!(
                    private["arguments"],
                    json!({"index":index.to_string(),"before":before.to_string()})
                );
                if index > 1 {
                    assert_eq!(
                        private["invocationWrites"]["loop/last"]["value"],
                        (index - 1).to_string()
                    );
                }
                let response = serde_json::from_value(json!({
                    "protocolVersion":2,"requestId":request["requestId"],"attemptId":attempt,
                    "operation":request["operation"],"capability":request["capability"],"schema":request["schema"],
                    "outcome":"value","value":index.to_string()
                })).unwrap();
                execution.resume_typed(response).unwrap();
            }
        }
        let result = execution.advance().unwrap();
        assert_eq!(result["status"], "completed");
        assert_eq!(result["result"], expected);
        let session = execution.session.as_mut().unwrap();
        let relation = serde_json::from_slice(CIRCUIT).unwrap();
        let completion = session.private_completion(&relation).unwrap();
        if enabled {
            assert_eq!(completion["hostWrites"]["loop/last"]["value"], "3");
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
