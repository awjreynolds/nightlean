#![cfg(feature = "zkir-321")]

use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value, json};
use std::collections::BTreeMap;

#[test]
fn copied_values_preserve_checks_disclosure_and_guarded_effects() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/native-copy/321/NativeCopy.store.impact.json"
    ))
    .unwrap();
    let source = include_str!("fixtures/native-copy/321/NativeCopy.store.zkir");
    let ir = IrSource::load(source.as_bytes()).unwrap();
    let instructions: Value = serde_json::from_str(source).unwrap();
    assert!(
        instructions["instructions"]
            .as_array()
            .unwrap()
            .iter()
            .any(|op| op["op"] == "copy")
    );

    let state = |stored: &str| {
        create_state(&plan, &BTreeMap::from([("stored".into(), json!(stored))])).unwrap()
    };
    let initial = state("1");
    let execute = |enabled: bool, expected: &str| {
        prepare(
            &plan,
            &BTreeMap::from([
                ("amount".into(), json!("9")),
                (
                    "payload".into(),
                    json!({"kind":"bytes","values":(0..32).collect::<Vec<u8>>()}),
                ),
                ("enabled".into(), json!(enabled)),
                ("expected".into(), json!(expected)),
            ]),
            &initial,
            &INITIAL_PARAMETERS,
            Default::default(),
        )
        .unwrap()
    };
    for enabled in [true, false] {
        let result = execute(enabled, "9");
        check(&result, &ir).unwrap();
        assert_eq!(
            result.returns_json(),
            BTreeMap::from([
                ("copiedByte".into(), json!("31")),
                ("copiedEnabled".into(), json!(enabled)),
            ])
        );
        assert_eq!(
            result.after.state,
            if enabled { state("9") } else { initial.clone() }
        );
    }
    assert!(check(&execute(true, "8"), &ir).is_err());
}
