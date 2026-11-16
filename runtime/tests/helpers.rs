use nightlean_runtime::{Environment, Expr, Value, canonical_field, evaluate};
use serde_json::json;

fn expression(value: serde_json::Value) -> Expr {
    serde_json::from_value(value).unwrap()
}

#[test]
fn helper_locals_preserve_type_and_restore_outer_bindings() {
    let mut env = Environment::new();
    env.insert("x".into(), Value::Native(canonical_field("9").unwrap()));
    let local = expression(json!({
        "tag": "let", "name": "x", "value": {"tag": "bool", "value": true},
        "body": {"tag": "eq", "left": {"tag": "reference", "name": "x"},
                 "right": {"tag": "bool", "value": true}}
    }));
    assert_eq!(evaluate(&local, &env).unwrap(), Value::Bool(true));
    assert_eq!(env["x"], Value::Native(canonical_field("9").unwrap()));
    let unsigned = expression(json!({
        "tag": "let", "name": "n", "value": {"tag": "uint", "maximum": "7", "value": "3"},
        "body": {"tag": "uadd", "maximum": "14",
                 "left": {"tag": "reference", "name": "n"},
                 "right": {"tag": "reference", "name": "n"}}
    }));
    assert!(matches!(evaluate(&unsigned, &env).unwrap(), Value::UInt {number, maximum}
        if number == 6_u32.into() && maximum == 14_u32.into()));
}

#[test]
fn helper_arguments_execute_before_body_even_when_unused() {
    let unused = expression(json!({
        "tag": "let", "name": "unused",
        "value": {"tag": "cast", "type": "UIntRange<1>",
                  "value": {"tag": "constant", "value": "1"}},
        "body": {"tag": "reference", "name": "missing_body"}
    }));
    let error = evaluate(&unused, &Environment::new()).unwrap_err().to_string();
    assert!(!error.contains("missing_body"), "{error}");
    assert_eq!(error, "unsigned value outside declared type");
}

#[test]
fn helper_assertions_fail_before_body_and_require_boolean() {
    let failed = expression(json!({
        "tag": "assertThen", "condition": {"tag": "bool", "value": false},
        "body": {"tag": "reference", "name": "missing_body"}
    }));
    assert_eq!(evaluate(&failed, &Environment::new()).unwrap_err().to_string(), "helper assertion failed");
    let wrong = expression(json!({
        "tag": "assertThen", "condition": {"tag": "constant", "value": "1"},
        "body": {"tag": "constant", "value": "9"}
    }));
    assert!(evaluate(&wrong, &Environment::new()).unwrap_err().to_string().contains("expected Bool"));
}

#[test]
fn helper_lexical_bindings_evaluate_arguments_left_to_right() {
    let ordered = expression(json!({
        "tag": "let", "name": "first",
        "value": {"tag": "reference", "name": "missing_left"},
        "body": {"tag": "let", "name": "second",
                 "value": {"tag": "reference", "name": "missing_right"},
                 "body": {"tag": "constant", "value": "0"}}
    }));
    let error = evaluate(&ordered, &Environment::new()).unwrap_err().to_string();
    assert!(error.contains("missing_left"), "{error}");
}
