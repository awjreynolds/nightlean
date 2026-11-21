#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Db, Expr, Instruction, Plan, check, construct_state, constructor::decode_opaque_string,
    field_value, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::json;
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn cell<'a>(
    plan: &Plan,
    state: &'a ChargedState<Db>,
    name: &str,
) -> &'a base_crypto::fab::AlignedValue {
    let slot = plan
        .state
        .iter()
        .position(|decl| decl.name == name)
        .unwrap();
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Cell(value) = root.get(slot).unwrap() else {
        panic!("expected metadata cell")
    };
    value
}

#[test]
fn constructor_binds_public_metadata_and_rejects_sealed_mutation() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/constructor-metadata/321/ConstructorMetadata.inspect.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/constructor-metadata/321/ConstructorMetadata.inspect.zkir")
            .as_slice(),
    )
    .unwrap();
    let name = "Token\0夜";
    let arguments = BTreeMap::from([
        ("name_".into(), json!(name)),
        ("symbol_".into(), json!("NOC")),
        ("decimals_".into(), json!("6")),
    ]);
    let initial = construct_state(&plan, &arguments).unwrap();
    let mut noncanonical = arguments.clone();
    noncanonical.insert("name_".into(), json!("Token 夜\0"));
    let error = construct_state(&plan, &noncanonical)
        .err()
        .expect("state construction must reject a trailing NUL");
    assert!(format!("{error:#}").contains("opaque string has trailing zero bytes"));
    noncanonical.insert("name_".into(), json!(""));
    let empty_name = construct_state(&plan, &noncanonical).unwrap();
    assert_eq!(decode_opaque_string(cell(&plan, &empty_name, "name")).unwrap(), "");
    assert_eq!(
        decode_opaque_string(cell(&plan, &initial, "name")).unwrap(),
        name
    );
    assert_eq!(cell(&plan, &initial, "name").value.0[0].0, name.as_bytes());
    assert_eq!(
        decode_opaque_string(cell(&plan, &initial, "symbol")).unwrap(),
        "NOC"
    );
    assert_eq!(
        decode_opaque_string(cell(&plan, &initial, "version")).unwrap(),
        "v1"
    );
    assert_eq!(
        cell(&plan, &initial, "decimals"),
        &field_value(Fr::from(6u64))
    );
    assert_eq!(
        cell(&plan, &initial, "initialized"),
        &field_value(Fr::from(1u64))
    );
    assert_eq!(
        cell(&plan, &initial, "supply"),
        &field_value(Fr::from(0u64))
    );
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let execution = prepare(&plan, &BTreeMap::new(), &initial, params, address).unwrap();
    check(&execution, &circuit).unwrap();
    assert_eq!(execution.after.state, initial);

    let mut missing = arguments.clone();
    missing.remove("name_");
    assert!(construct_state(&plan, &missing).is_err());
    let mut oversized = arguments.clone();
    oversized.insert("decimals_".into(), json!("256"));
    assert!(construct_state(&plan, &oversized).is_err());
    let mut extra = arguments;
    extra.insert("unknown".into(), json!("unused"));
    assert!(construct_state(&plan, &extra).is_err());

    let slot = plan
        .state
        .iter()
        .position(|decl| decl.name == "decimals")
        .unwrap();
    let mut forged = plan.clone();
    forged.operations.extend([
        Instruction::Push {
            storage: false,
            expression: Expr::Constant {
                value: slot.to_string(),
            },
            alignment: "field".into(),
        },
        Instruction::Push {
            storage: true,
            expression: Expr::Constant { value: "7".into() },
            alignment: "field".into(),
        },
        Instruction::Insert { n: 1 },
    ]);
    let error = prepare(&forged, &BTreeMap::new(), &initial, params, address)
        .err()
        .expect("sealed cell mutation must reject");
    assert!(error.to_string().contains("sealed state cell"), "{error:#}");
}
