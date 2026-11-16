use nightlean_runtime::{
    control::{Response, Session},
    host,
};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;

fn c(n: u32) -> Json {
    json!({"tag":"constant","value":n.to_string()})
}
fn b(v: bool) -> Json {
    json!({"tag":"bool","value":v})
}
fn w(name: &str, ty: &str) -> Json {
    json!({"tag":"witness","name":name,"type":ty})
}
fn disclose(value: Json) -> Json {
    json!({"tag":"disclose","value":value})
}
fn ret(value: Json) -> Json {
    json!({"tag":"return","value":value})
}
fn expr(value: Json) -> Json {
    json!({"tag":"evaluate","value":value})
}
fn plan(body: Vec<Json>, witnesses: Vec<Json>) -> Json {
    json!({"schemaVersion":1,"kind":"host-control","name":"control-test","inputs":[],"witnesses":witnesses,"functions":[{"id":"s0d0","name":"main","parameters":[],"resultType":"Native","body":body}],"entry":"s0d0","limits":{"maxSteps":131072}})
}
fn context(witnesses: &[Json]) -> host::Context {
    let providers:Vec<_>=witnesses.iter().map(|w|json!({"input":w["name"],"operation":if w["type"]=="Bool"{"witness.bool.v1"}else{"witness.native.v1"},"capability":"store","arguments":{}})).collect();
    serde_json::from_value(json!({"protocolVersion":1,"namespace":"test","baseRevision":"r0","attemptId":"a".repeat(64),"capabilities":[{"id":"store","namespace":"test","keyPrefix":"local/","operations":["witness.bool.v1","witness.native.v1","private_state.stage.v1","private_state.compare_exchange.v1"]}],"operations":[{"operation":"witness.bool.v1","argumentSchema":{},"resultSchema":"Bool"},{"operation":"witness.native.v1","argumentSchema":{},"resultSchema":"Native"}],"providers":providers,"commitCapability":"store","limits":{"requests":64,"writes":64,"privateBytes":65536}})).unwrap()
}
fn begin(p: Json) -> Session {
    Session::from_json(
        p.clone(),
        BTreeMap::new(),
        context(p["witnesses"].as_array().unwrap()),
    )
    .unwrap()
}
fn response(request: &Json, value: Json) -> Response {
    serde_json::from_value(json!({"abiVersion":1,"requestId":request["id"],"operation":request["operation"],"capability":request["capability"],"schema":request["schema"],"value":value})).unwrap()
}
fn drive(session: &mut Session) -> (Json, Vec<String>) {
    let mut calls = vec![];
    loop {
        let status = session.advance().unwrap();
        if status["status"] != "need_host" {
            return (status, calls);
        }
        let request = &status["request"];
        let name = request["name"].as_str().unwrap();
        calls.push(name.to_owned());
        if name == "right" {
            assert_eq!(
                session.private_request().unwrap()["invocationWrites"]["local/item"]["value"],
                "9"
            );
        }
        let value = if name == "flag" {
            json!(true)
        } else if name == "left" {
            json!("11")
        } else {
            json!("22")
        };
        session.resume(response(request, value)).unwrap();
    }
}

#[test]
fn registered_inactive_callbacks_and_private_stages_do_not_run() {
    let witnesses = vec![json!({"name":"unused","type":"Native"})];
    let source = plan(
        vec![
            json!({"tag":"if","condition":b(false),"yes":[expr(w("unused","Native")),json!({"tag":"stage","capability":"store","key":"local/item","type":"Native","value":c(9)}),ret(c(0))],"no":[ret(c(7))]}),
        ],
        witnesses,
    );
    let mut session = begin(source);
    let (status, calls) = drive(&mut session);
    assert_eq!(status["result"], "7");
    assert!(calls.is_empty());
    assert_eq!(session.private_trace()["events"], json!([]));
    assert!(status.get("trace").is_none());
}
#[test]
fn active_callbacks_suspend_once_in_order_and_private_staging_is_local() {
    let witnesses = vec![
        json!({"name":"flag","type":"Bool"}),
        json!({"name":"left","type":"Native"}),
        json!({"name":"right","type":"Native"}),
    ];
    let source = plan(
        vec![
            json!({"tag":"if","condition":disclose(w("flag","Bool")),"yes":[expr(w("left","Native")),json!({"tag":"stage","capability":"store","key":"local/item","type":"Native","value":c(9)}),ret(disclose(w("right","Native")))],"no":[ret(c(0))]}),
        ],
        witnesses,
    );
    let mut session = begin(source);
    let first = session.advance().unwrap();
    assert_eq!(first, session.advance().unwrap());
    assert!(session.private_request().is_ok());
    let mut wrong = response(&first["request"], json!(true));
    wrong.request_id += 1;
    assert!(session.resume(wrong).is_err());
    assert_eq!(first, session.advance().unwrap());
    session
        .resume(response(&first["request"], json!(true)))
        .unwrap();
    let (result, mut calls) = drive(&mut session);
    calls.insert(0, "flag".into());
    assert_eq!(calls, vec!["flag", "left", "right"]);
    assert_eq!(result["result"], "22");
    assert_eq!(
        session.private_trace()["events"],
        json!(["witness:flag", "witness:left", "stage", "witness:right"])
    );
    assert!(session.stage(serde_json::from_value(json!({"abiVersion":1,"operation":"private_state.stage.v1","capability":"store","key":"local/item","type":"Native","value":"3"})).unwrap()).is_err());
}
#[test]
fn inactive_assertions_casts_and_short_circuit_operands_are_skipped() {
    let bad_cast = json!({"tag":"cast","type":"UIntRange<1>","value":c(1)});
    let source = plan(
        vec![
            json!({"tag":"if","condition":b(false),"yes":[json!({"tag":"assert","condition":b(false)}),expr(bad_cast)],"no":[]}),
            expr(json!({"tag":"and","left":b(false),"right":w("unused","Bool")})),
            expr(json!({"tag":"or","left":b(true),"right":w("unused","Bool")})),
            ret(c(9)),
        ],
        vec![json!({"name":"unused","type":"Bool"})],
    );
    let mut session = begin(source);
    let (status, calls) = drive(&mut session);
    assert_eq!(status["result"], "9");
    assert!(calls.is_empty());
}
#[test]
fn both_branches_are_checked_and_join_requires_comparable_types() {
    let unknown = plan(
        vec![ret(
            json!({"tag":"if","condition":b(true),"yes":c(1),"no":{"tag":"reference","name":"missing"}}),
        )],
        vec![],
    );
    assert!(Session::from_json(unknown, BTreeMap::new(), context(&[])).is_err());
    let incompatible = plan(
        vec![ret(
            json!({"tag":"if","condition":b(true),"yes":c(1),"no":b(false)}),
        )],
        vec![],
    );
    assert!(Session::from_json(incompatible, BTreeMap::new(), context(&[])).is_err());
}
#[test]
fn payload_release_does_not_release_statement_guard_or_return_continuation() {
    for flag in [true, false] {
        let mut source = plan(
            vec![
                json!({"tag":"if","condition":{"tag":"reference","name":"secret"},"yes":[ret(disclose(c(1)))],"no":[]}),
                ret(disclose(c(2))),
            ],
            vec![],
        );
        source["inputs"] = json!([{"name":"secret","type":"Bool","visibility":"private"}]);
        source["functions"][0]["parameters"] = json!([{"name":"secret","type":"Bool"}]);
        let mut session = Session::from_json(
            source,
            BTreeMap::from([("secret".into(), json!(flag))]),
            context(&[]),
        )
        .unwrap();
        assert_eq!(session.advance().unwrap()["status"], "failed");
    }
}
#[test]
fn whole_conditional_release_authorizes_its_value_and_nested_private_guards_accumulate() {
    let mut source = plan(
        vec![ret(disclose(
            json!({"tag":"if","condition":{"tag":"reference","name":"secret"},"yes":c(1),"no":c(2)}),
        ))],
        vec![],
    );
    source["inputs"] = json!([{"name":"secret","type":"Bool","visibility":"private"}]);
    source["functions"][0]["parameters"] = json!([{"name":"secret","type":"Bool"}]);
    let mut session = Session::from_json(
        source,
        BTreeMap::from([("secret".into(), json!(false))]),
        context(&[]),
    )
    .unwrap();
    assert_eq!(session.advance().unwrap()["result"], "2");
}
#[test]
fn cancellation_drops_pending_request_and_rejects_late_responses() {
    let source = plan(
        vec![ret(disclose(w("active", "Native")))],
        vec![json!({"name":"active","type":"Native"})],
    );
    let mut session = begin(source);
    let request = session.advance().unwrap();
    session.cancel().unwrap();
    assert!(session.private_request().is_err());
    assert!(
        session
            .resume(response(&request["request"], json!("9")))
            .is_err()
    );
    assert_eq!(session.advance().unwrap()["status"], "cancelled");
}
#[test]
fn missing_inactive_registration_and_raised_fuel_are_rejected() {
    let source = plan(
        vec![ret(c(1))],
        vec![json!({"name":"unused","type":"Native"})],
    );
    assert!(Session::from_json(source, BTreeMap::new(), context(&[])).is_err());
    let mut source = plan(vec![ret(c(1))], vec![]);
    source["limits"]["maxSteps"] = json!(131073);
    assert!(Session::from_json(source, BTreeMap::new(), context(&[])).is_err());
}

fn abi_take(token: u64, private: bool) -> Json {
    use nightlean_runtime::control_ffi::*;
    let mut length = 0;
    let mut written = 0;
    if private {
        assert_eq!(
            unsafe { nightlean_control_result_length(token, &mut length) },
            INVALID_HANDLE
        );
        assert_eq!(
            unsafe { nightlean_control_private_length(token, &mut length) },
            OK
        );
    } else {
        assert_eq!(
            unsafe { nightlean_control_result_length(token, &mut length) },
            OK
        );
    }
    let mut bytes = vec![0; length];
    let status = unsafe {
        if private {
            nightlean_control_private_copy(token, bytes.as_mut_ptr(), length, &mut written)
        } else {
            nightlean_control_result_copy(token, bytes.as_mut_ptr(), length, &mut written)
        }
    };
    assert_eq!(status, OK);
    assert_eq!(written, length);
    assert_eq!(
        if private {
            nightlean_control_private_free(token)
        } else {
            nightlean_control_result_free(token)
        },
        OK
    );
    serde_json::from_slice(&bytes).unwrap()
}
fn abi_drive(source: Json) -> (Json, Json, Vec<String>) {
    use nightlean_runtime::control_ffi::*;
    let envelope = json!({"abiVersion":1,"plan":source,"inputs":{},"hostContext":context_json(source["witnesses"].as_array().unwrap())});
    let bytes = serde_json::to_vec(&envelope).unwrap();
    let mut handle = 0;
    assert_eq!(
        unsafe { nightlean_control_begin(bytes.as_ptr(), bytes.len(), &mut handle) },
        OK
    );
    let mut calls = vec![];
    let result = loop {
        let mut token = 0;
        assert_eq!(unsafe { nightlean_control_advance(handle, &mut token) }, OK);
        let result = abi_take(token, false);
        if result["status"] != "need_host" {
            break result;
        }
        let request = &result["request"];
        let name = request["name"].as_str().unwrap();
        calls.push(name.into());
        let value = if name == "flag" {
            json!(true)
        } else if name == "left" {
            json!("11")
        } else {
            json!("22")
        };
        let bytes=serde_json::to_vec(&json!({"abiVersion":1,"requestId":request["id"],"operation":request["operation"],"capability":request["capability"],"schema":request["schema"],"value":value})).unwrap();
        assert_eq!(
            unsafe { nightlean_control_resume(handle, bytes.as_ptr(), bytes.len(), &mut token) },
            OK
        );
        abi_take(token, false);
    };
    let mut token = 0;
    assert_eq!(
        unsafe { nightlean_control_private_trace(handle, &mut token) },
        OK
    );
    let trace = abi_take(token, true);
    assert_eq!(nightlean_control_free(handle), OK);
    (result, trace, calls)
}
fn context_json(witnesses: &[Json]) -> Json {
    let providers:Vec<_>=witnesses.iter().map(|w|json!({"input":w["name"],"operation":if w["type"]=="Bool"{"witness.bool.v1"}else{"witness.native.v1"},"capability":"store","arguments":{}})).collect();
    json!({"protocolVersion":1,"namespace":"test","baseRevision":"r0","attemptId":"a".repeat(64),"capabilities":[{"id":"store","namespace":"test","keyPrefix":"local/","operations":["witness.bool.v1","witness.native.v1","private_state.stage.v1","private_state.compare_exchange.v1"]}],"operations":[{"operation":"witness.bool.v1","argumentSchema":{},"resultSchema":"Bool"},{"operation":"witness.native.v1","argumentSchema":{},"resultSchema":"Native"}],"providers":providers,"commitCapability":"store","limits":{"requests":64,"writes":64,"privateBytes":65536}})
}
#[test]
fn direct_and_c_abi_adapters_match_results_errors_and_private_effect_traces() {
    let witnesses = vec![
        json!({"name":"flag","type":"Bool"}),
        json!({"name":"left","type":"Native"}),
        json!({"name":"right","type":"Native"}),
    ];
    let active = plan(
        vec![
            json!({"tag":"if","condition":disclose(w("flag","Bool")),"yes":[expr(w("left","Native")),json!({"tag":"stage","capability":"store","key":"local/item","type":"Native","value":c(9)}),ret(disclose(w("right","Native")))],"no":[ret(c(0))]}),
        ],
        witnesses,
    );
    let failed = plan(
        vec![
            expr(disclose(w("left", "Native"))),
            json!({"tag":"assert","condition":b(false)}),
            ret(c(0)),
        ],
        vec![json!({"name":"left","type":"Native"})],
    );
    let inactive = plan(
        vec![ret(
            json!({"tag":"if","condition":b(false),"yes":w("unused","Native"),"no":c(7)}),
        )],
        vec![json!({"name":"unused","type":"Native"})],
    );
    for source in [active, failed, inactive] {
        let mut direct = begin(source.clone());
        let (result, calls) = drive(&mut direct);
        let trace = direct.private_trace();
        let (abi_result, abi_trace, abi_calls) = abi_drive(source);
        assert_eq!(result, abi_result);
        assert_eq!(trace, abi_trace);
        assert_eq!(calls, abi_calls);
    }
}

#[test]
fn actual_lean_source_plan_runs_registered_rust_callbacks_and_private_overlay() {
    let source: Json = serde_json::from_str(include_str!(
        "fixtures/control/conditionalProviders.control.json"
    ))
    .unwrap();
    let original = BTreeMap::from([("counter/value".to_owned(), json!("0"))]);
    for active in [false, true] {
        let mut descriptor = context_json(source["witnesses"].as_array().unwrap());
        descriptor["capabilities"][0]["keyPrefix"] = json!("counter/");
        let mut session = Session::from_json(
            source.clone(),
            BTreeMap::from([("active".into(), json!(active))]),
            serde_json::from_value(descriptor).unwrap(),
        )
        .unwrap();
        let callbacks: BTreeMap<&str, fn(&Json) -> Json> = BTreeMap::from([
            ("flag", (|_: &Json| json!(true)) as fn(&Json) -> Json),
            ("left", (|_: &Json| json!("11")) as fn(&Json) -> Json),
            (
                "right",
                (|private: &Json| {
                    assert_eq!(private["invocationWrites"]["counter/value"]["value"], "1");
                    json!("22")
                }) as fn(&Json) -> Json,
            ),
        ]);
        let mut counts = BTreeMap::from([("flag", 0), ("left", 0), ("right", 0)]);
        let result = loop {
            let status = session.advance().unwrap();
            if status["status"] != "need_host" {
                break status;
            }
            let request = &status["request"];
            let name = request["name"].as_str().unwrap();
            let args = session.private_request().unwrap();
            *counts.get_mut(name).unwrap() += 1;
            let value = callbacks[name](&args);
            session.resume(response(request, value)).unwrap();
        };
        assert_eq!(result["result"], if active { "22" } else { "7" });
        assert!(counts.values().all(|count| *count == usize::from(active)));
        assert_eq!(
            session.private_trace()["events"],
            if active {
                json!(["witness:flag", "witness:left", "stage", "witness:right"])
            } else {
                json!([])
            }
        );
        assert_eq!(original["counter/value"], "0");
    }
}
#[test]
fn actual_lean_failure_and_inactive_plans_have_expected_host_behavior() {
    for (file, expected, value) in [
        (
            include_str!("fixtures/control/activeFailure.control.json"),
            "failed",
            Json::Null,
        ),
        (
            include_str!("fixtures/control/inactiveFailure.control.json"),
            "completed",
            json!("9"),
        ),
        (
            include_str!("fixtures/control/lazyReturn.control.json"),
            "completed",
            json!("5"),
        ),
        (
            include_str!("fixtures/control/lazyExpression.control.json"),
            "completed",
            json!("2"),
        ),
        (
            include_str!("fixtures/control/shortCircuit.control.json"),
            "completed",
            json!(true),
        ),
    ] {
        let source: Json = serde_json::from_str(file).unwrap();
        let mut session = begin(source);
        let (result, calls) = drive(&mut session);
        assert_eq!(result["status"], expected);
        if expected == "completed" {
            assert_eq!(result["result"], value);
        } else {
            assert_eq!(result["error"]["code"], "execution_rejected");
        }
        assert!(calls.is_empty());
        assert_eq!(session.private_trace()["events"], json!([]));
    }
}

#[test]
fn typed_response_binding_failures_preserve_pending_continuation() {
    let source = plan(
        vec![ret(disclose(w("active", "Native")))],
        vec![json!({"name":"active","type":"Native"})],
    );
    let mut session = begin(source);
    let request = session.advance().unwrap();
    for changed in ["operation", "capability", "schema", "value"] {
        let mut response = response(&request["request"], json!("9"));
        match changed {
            "operation" => response.operation = "other.v1".into(),
            "capability" => response.capability = "other".into(),
            "schema" => response.schema = "Bool".into(),
            _ => response.value = json!("09"),
        };
        assert!(session.resume(response).is_err());
        assert_eq!(request, session.advance().unwrap());
    }
    session
        .resume(response(&request["request"], json!("9")))
        .unwrap();
    assert!(
        session
            .resume(response(&request["request"], json!("9")))
            .is_err()
    );
    assert_eq!(session.advance().unwrap()["result"], "9");
    assert_eq!(session.private_trace()["events"], json!(["witness:active"]));
}
#[test]
fn typed_call_arguments_execute_once_and_function_return_does_not_escape_caller() {
    let mut source = plan(
        vec![ret(
            json!({"tag":"disclose","value":{"tag":"binary","operation":"add","left":{"tag":"call","function":"s0d1","arguments":[w("left","Native"),w("right","Native")]},"right":c(1)}}),
        )],
        vec![
            json!({"name":"left","type":"Native"}),
            json!({"name":"right","type":"Native"}),
        ],
    );
    source["functions"].as_array_mut().unwrap().push(json!({"id":"s0d1","name":"duplicateFirst","parameters":[{"name":"a","type":"Native"},{"name":"unused","type":"Native"}],"resultType":"Native","body":[ret(json!({"tag":"binary","operation":"add","left":{"tag":"reference","name":"a"},"right":{"tag":"reference","name":"a"}})),json!({"tag":"assert","condition":b(false)})]}));
    let mut session = begin(source);
    let mut calls = vec![];
    loop {
        let status = session.advance().unwrap();
        if status["status"] != "need_host" {
            assert_eq!(status["result"], "23");
            break;
        }
        let request = &status["request"];
        calls.push(request["name"].as_str().unwrap().to_owned());
        session
            .resume(response(
                request,
                if request["name"] == "left" {
                    json!("11")
                } else {
                    json!("22")
                },
            ))
            .unwrap();
    }
    assert_eq!(calls, vec!["left", "right"]);
    assert_eq!(
        session.private_trace()["events"],
        json!(["witness:left", "witness:right"])
    );
}
#[test]
fn static_resource_limits_cover_shared_doubling_calls_and_raw_tree_depth() {
    let mut source = plan(vec![], vec![]);
    let mut functions = vec![];
    for n in 0..=12 {
        functions.push(json!({"id":format!("s0d{n}"),"name":format!("f{n}"),"parameters":[],"resultType":"Unit","body":if n==0{vec![]}else{vec![expr(json!({"tag":"call","function":format!("s0d{}",n-1),"arguments":[]})),expr(json!({"tag":"call","function":format!("s0d{}",n-1),"arguments":[]}))]}}));
    }
    source["functions"] = json!(functions);
    source["entry"] = json!("s0d12");
    let error = Session::from_json(source, BTreeMap::new(), context(&[]))
        .err()
        .unwrap();
    assert!(error.to_string().contains("expanded node"));
    let mut value = c(1);
    for _ in 0..129 {
        value = json!({"tag":"cast","type":"Native","value":value});
    }
    assert!(
        Session::from_json(
            plan(vec![ret(value)], vec![]),
            BTreeMap::new(),
            context(&[])
        )
        .is_err()
    );
}
#[test]
fn direct_stage_rejects_unauthorized_keys_and_cancelled_invocations() {
    let mut session = begin(plan(
        vec![ret(disclose(w("right", "Native")))],
        vec![json!({"name":"right","type":"Native"})],
    ));
    session.advance().unwrap();
    let stage = |key: &str, value: &str| {
        serde_json::from_value(json!({"abiVersion":1,"operation":"private_state.stage.v1","capability":"store","key":key,"type":"Native","value":value})).unwrap()
    };
    assert!(session.stage(stage("outside/value", "1")).is_err());
    assert_eq!(
        session.private_request().unwrap()["invocationWrites"],
        json!({})
    );
    session.stage(stage("local/item", "3")).unwrap();
    assert_eq!(
        session.private_request().unwrap()["invocationWrites"]["local/item"]["value"],
        "3"
    );
    session.cancel().unwrap();
    assert!(session.private_request().is_err());
    assert!(session.stage(stage("local/item", "4")).is_err());
}

#[test]
fn control_abi_clears_outputs_and_checks_handles_and_copy_capacity() {
    use nightlean_runtime::control_ffi::*;
    let source = plan(vec![ret(c(1))], vec![]);
    let bytes = serde_json::to_vec(
        &json!({"abiVersion":1,"plan":source,"inputs":{},"hostContext":context_json(&[])}),
    )
    .unwrap();
    let mut session = 99;
    assert_eq!(
        unsafe { nightlean_control_begin(std::ptr::null(), 1, &mut session) },
        INVALID_ARGUMENT
    );
    assert_eq!(session, 0);
    assert_eq!(
        unsafe { nightlean_control_begin(bytes.as_ptr(), bytes.len(), &mut session) },
        OK
    );
    let mut token = 99;
    assert_eq!(
        unsafe { nightlean_control_advance(session, &mut token) },
        OK
    );
    let mut length = 0;
    assert_eq!(
        unsafe { nightlean_control_result_length(token, &mut length) },
        OK
    );
    let mut buffer = vec![0; length];
    let mut written = 99;
    assert_eq!(
        unsafe {
            nightlean_control_result_copy(token, buffer.as_mut_ptr(), length - 1, &mut written)
        },
        BUFFER_TOO_SMALL
    );
    assert_eq!(written, 0);
    assert_eq!(
        unsafe { nightlean_control_result_copy(token, buffer.as_mut_ptr(), length, &mut written) },
        OK
    );
    assert_eq!(written, length);
    assert_eq!(nightlean_control_result_free(token), OK);
    assert_eq!(nightlean_control_result_free(token), INVALID_HANDLE);
    assert_eq!(nightlean_control_free(session), OK);
    token = 99;
    assert_eq!(
        unsafe { nightlean_control_advance(session, &mut token) },
        INVALID_HANDLE
    );
    assert_eq!(token, 0);
}

#[test]
fn nested_partial_returns_preserve_control_through_outer_fallthrough() {
    for flag in [false, true] {
        let mut source = plan(
            vec![
                json!({"tag":"if","condition":b(true),"yes":[json!({"tag":"if","condition":{"tag":"reference","name":"secret"},"yes":[ret(c(1))],"no":[]})],"no":[]}),
                ret(disclose(c(2))),
            ],
            vec![],
        );
        source["inputs"] = json!([{"name":"secret","type":"Bool","visibility":"private"}]);
        source["functions"][0]["parameters"] = json!([{"name":"secret","type":"Bool"}]);
        let mut session = Session::from_json(
            source,
            BTreeMap::from([("secret".into(), json!(flag))]),
            context(&[]),
        )
        .unwrap();
        assert_eq!(session.advance().unwrap()["status"], "failed");
    }
}
#[test]
fn lazy_unit_expression_is_typed_and_evaluates_only_selected_branch() {
    let mut source = plan(
        vec![expr(
            json!({"tag":"if","condition":b(true),"yes":{"tag":"unit"},"no":{"tag":"unit"}}),
        )],
        vec![],
    );
    source["functions"][0]["resultType"] = json!("Unit");
    let mut session = begin(source);
    let result = session.advance().unwrap();
    assert_eq!(result["status"], "completed");
    assert_eq!(result["result"], Json::Null);
}
#[test]
fn actual_source_order_fixture_invokes_both_registered_callbacks_left_to_right() {
    let source: Json =
        serde_json::from_str(include_str!("fixtures/control/witnessOrder.control.json")).unwrap();
    let mut session = begin(source);
    let mut calls = vec![];
    loop {
        let status = session.advance().unwrap();
        if status["status"] != "need_host" {
            assert_eq!(status["result"], "33");
            break;
        }
        let request = &status["request"];
        let name = request["name"].as_str().unwrap();
        calls.push(name.to_owned());
        session
            .resume(response(
                request,
                if name == "left" {
                    json!("11")
                } else {
                    json!("22")
                },
            ))
            .unwrap();
    }
    assert_eq!(calls, vec!["left", "right"]);
    assert_eq!(
        session.private_trace()["events"],
        json!(["witness:left", "witness:right"])
    );
}

#[test]
fn actual_source_unit_and_constant_inactive_returns_interoperate() {
    let unit: Json = serde_json::from_str(include_str!(
        "fixtures/control/unitConditional.control.json"
    ))
    .unwrap();
    let mut session = begin(unit);
    assert_eq!(session.advance().unwrap()["result"], Json::Null);
    for flag in [false, true] {
        for (file, value) in [
            (
                include_str!("fixtures/control/unitPrivateBranches.control.json"),
                Json::Null,
            ),
            (
                include_str!("fixtures/control/constantInactiveReturn.control.json"),
                json!("2"),
            ),
        ] {
            let source: Json = serde_json::from_str(file).unwrap();
            let mut session = Session::from_json(
                source,
                BTreeMap::from([("flag".into(), json!(flag))]),
                context(&[]),
            )
            .unwrap();
            let status = session.advance().unwrap();
            assert_eq!(status["status"], "completed");
            assert_eq!(status["result"], value);
            assert_eq!(session.private_trace()["events"], json!([]));
        }
    }
}
#[test]
fn constant_abstract_returns_cover_casts_arithmetic_locals_and_pure_helpers() {
    let equal = json!({"tag":"eq","left":c(0),"right":c(1)});
    for condition in [
        equal.clone(),
        json!({"tag":"cast","type":"Bool","value":c(0)}),
        json!({"tag":"and","left":{"tag":"reference","name":"secret"},"right":b(false)}),
        json!({"tag":"reference","name":"constant"}),
        json!({"tag":"call","function":"s0d1","arguments":[{"tag":"reference","name":"secret"}]}),
    ] {
        for flag in [false, true] {
            let mut source = plan(
                vec![
                    json!({"tag":"bind","name":"constant","type":"Bool","value":equal}),
                    json!({"tag":"if","condition":{"tag":"reference","name":"secret"},"yes":[json!({"tag":"if","condition":condition,"yes":[ret(c(1))],"no":[]})],"no":[]}),
                    ret(c(2)),
                ],
                vec![],
            );
            source["inputs"] = json!([{"name":"secret","type":"Bool","visibility":"private"}]);
            source["functions"][0]["parameters"] = json!([{"name":"secret","type":"Bool"}]);
            source["functions"].as_array_mut().unwrap().push(json!({"id":"s0d1","name":"alwaysFalse","parameters":[{"name":"p","type":"Bool"}],"resultType":"Bool","body":[json!({"tag":"if","condition":{"tag":"reference","name":"p"},"yes":[ret(b(false))],"no":[ret(b(false))]})]}));
            let mut session = Session::from_json(
                source,
                BTreeMap::from([("secret".into(), json!(flag))]),
                context(&[]),
            )
            .unwrap();
            assert_eq!(session.advance().unwrap()["result"], "2");
        }
    }
}

#[test]
fn actual_source_single_branch_witness_and_overlay_are_lazy() {
    let source: Json =
        serde_json::from_str(include_str!("fixtures/control/branchWitness.control.json")).unwrap();
    for active in [false, true] {
        let mut descriptor = context_json(source["witnesses"].as_array().unwrap());
        descriptor["capabilities"][0]["keyPrefix"] = json!("counter/");
        let mut session = Session::from_json(
            source.clone(),
            BTreeMap::from([("active".into(), json!(active))]),
            serde_json::from_value(descriptor).unwrap(),
        )
        .unwrap();
        let mut count = 0;
        let result = loop {
            let status = session.advance().unwrap();
            if status["status"] != "need_host" {
                break status;
            }
            count += 1;
            assert_eq!(status["request"]["name"], "chosen");
            assert_eq!(
                session.private_request().unwrap()["invocationWrites"]["counter/value"]["value"],
                "1"
            );
            session
                .resume(response(&status["request"], json!("22")))
                .unwrap();
        };
        assert_eq!(count, usize::from(active));
        assert_eq!(result["result"], if active { "22" } else { "7" });
        assert_eq!(
            session.private_trace()["events"],
            if active {
                json!(["stage", "witness:chosen"])
            } else {
                json!([])
            }
        );
    }
}
