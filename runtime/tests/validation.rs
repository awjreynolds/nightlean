mod common;
use noctium_runtime::{
    Expr, MODULUS, Plan, Value, canonical_field, environment, evaluate, field_decimal,
};
use serde_json::json;
use std::collections::BTreeMap;

fn expr(value: serde_json::Value) -> Expr {
    serde_json::from_value(value).unwrap()
}

#[test]
fn canonical_native_boundaries() {
    assert!(canonical_field(&"1".repeat(10_000)).is_err());
    for invalid in ["", "00", "042", "+1", "-1", " 1", MODULUS] {
        assert!(canonical_field(invalid).is_err());
    }
    for valid in [
        "0",
        "1",
        "256",
        "52435875175126190479447740508185965837690552500527637822603658699938581184512",
    ] {
        assert_eq!(field_decimal(canonical_field(valid).unwrap()), valid);
    }
}

#[test]
fn only_declared_public_outputs_leave_the_runtime() {
    let plan: Plan = serde_json::from_value(json!({
        "schemaVersion":1,"entrypoint":"claim",
        "circuit":{"inputs":[],"outputs":[{
            "name":"secret","visibility":"private","type":"Native",
            "expression":{"tag":"constant","value":"42"}
        }]},"state":[],"operations":[],"reads":[]
    }))
    .unwrap();
    let plan = common::selected(plan);
    assert!(environment(&plan, &BTreeMap::new()).is_err());
}

#[test]
fn eager_selection_and_type_errors_are_preserved() {
    let tree = expr(
        json!({"tag":"select","condition":{"tag":"bool","value":true},"yes":{"tag":"constant","value":"1"},"no":{"tag":"reference","name":"missing"}}),
    );
    assert!(evaluate(&tree, &BTreeMap::new()).is_err());
    let mismatch = expr(
        json!({"tag":"eq","left":{"tag":"constant","value":"1"},"right":{"tag":"bool","value":true}}),
    );
    assert!(evaluate(&mismatch, &BTreeMap::new()).is_err());
}

#[test]
fn native_arithmetic_wraps_at_field_modulus() {
    let tree = expr(
        json!({"tag":"add","left":{"tag":"constant","value":"52435875175126190479447740508185965837690552500527637822603658699938581184512"},"right":{"tag":"constant","value":"1"}}),
    );
    assert_eq!(
        evaluate(&tree, &BTreeMap::new()).unwrap(),
        Value::Native(canonical_field("0").unwrap())
    );
}

#[test]
fn official_poseidon_matches_qualified_public_fixture_vector() {
    let tree = expr(
        json!({"tag":"poseidon2","domain":"3","left":{"tag":"constant","value":"42"},"right":{"tag":"constant","value":"9"}}),
    );
    let Value::Native(result) = evaluate(&tree, &BTreeMap::new()).unwrap() else {
        panic!("wrong hash type")
    };
    assert_eq!(
        field_decimal(result),
        "16533581147424469099777953019315187868248076859940057971562926865714239641352"
    );
}

#[test]
fn input_schema_is_exact_and_boolean_inputs_are_not_coerced() {
    let plan:Plan=serde_json::from_value(json!({"schemaVersion":1,"entrypoint":"claim","circuit":{"inputs":[{"name":"x","type":"Bool","visibility":"private"}],"outputs":[]},"state":[],"operations":[],"reads":[]})).unwrap();
    let plan = common::selected(plan);
    for invalid in [
        json!({}),
        json!({"x":"true"}),
        json!({"x":true,"extra":false}),
    ] {
        assert!(environment(&plan, &serde_json::from_value(invalid).unwrap()).is_err());
    }
    assert!(environment(&plan, &serde_json::from_value(json!({"x":true})).unwrap()).is_ok());
    let mut unsupported = plan;
    unsupported.schema_version = 2;
    assert!(
        environment(
            &unsupported,
            &serde_json::from_value(json!({"x":true})).unwrap()
        )
        .is_err()
    );
}

#[test]
fn unknown_expression_variants_and_fields_reject() {
    assert!(serde_json::from_value::<Expr>(json!({"tag":"eval","code":"untrusted"})).is_err());
    assert!(
        serde_json::from_value::<Expr>(json!({"tag":"constant","value":"1","unknown":"x"}))
            .is_err()
    );
}

#[test]
fn unqualified_nonempty_map_state_rejects() {
    let plan:Plan=serde_json::from_value(json!({"schemaVersion":1,"entrypoint":"claim","circuit":{"inputs":[],"outputs":[]},"state":[{"name":"spent","kind":{"map":["Native","Bool"]}}],"operations":[],"reads":[]})).unwrap();
    let plan = common::selected(plan);
    let config = serde_json::from_value(json!({"spent":[["1",true]]})).unwrap();
    assert!(noctium_runtime::create_state(&plan, &config).is_err());
}

#[test]
fn state_read_after_write_uses_the_native_tentative_state() {
    let plan:Plan=serde_json::from_value(json!({"schemaVersion":1,"entrypoint":"claim","circuit":{"inputs":[],"outputs":[]},"state":[{"name":"root","kind":{"cell":"Native"}}],"operations":[
        {"op":"push","storage":false,"alignment":"field","expression":{"tag":"constant","value":"0"}},
        {"op":"push","storage":true,"alignment":"field","expression":{"tag":"constant","value":"2"}},
        {"op":"insert","n":1},{"op":"dup"},{"op":"index","slot":0,"pushPath":false},
        {"op":"popeq","alignment":"field","expression":{"tag":"reference","name":"post"}}
    ],"reads":[{"name":"post","type":"Native"}]})).unwrap();
    let plan = common::selected(plan);
    let state = noctium_runtime::create_state(
        &plan,
        &serde_json::from_value(json!({"root":"1"})).unwrap(),
    )
    .unwrap();
    let execution = noctium_runtime::prepare(
        &plan,
        &BTreeMap::new(),
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    assert_eq!(execution.preimage.public_transcript_outputs.len(), 1);
    assert_eq!(
        field_decimal(execution.preimage.public_transcript_outputs[0]),
        "2"
    );
}
