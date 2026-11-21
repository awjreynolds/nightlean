#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{Plan, Value, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires fresh ScalarMaybeAuthoringNative artifacts in NOCTIUM_SCALAR_MAYBE_AUTHORING_DIR"]
fn readable_scalar_maybe_returns_match_the_native_relation() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_SCALAR_MAYBE_AUTHORING_DIR")?);
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("ScalarMaybeAuthoringNative.consume.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("ScalarMaybeAuthoringNative.consume.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &BTreeMap::from([("amount".into(), json!("37"))]),
        &state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    check(&execution, &circuit)?;

    let returns = execution.returns_json();
    assert_eq!(
        returns["presentUIntOption"],
        json!({
            "kind": "struct",
            "id": "scalarMaybeAuthoring.MaybeUInt8",
            "fields": [
                {"name": "is_some", "value": {"kind": "bool", "value": true}},
                {"name": "value", "value": {"kind": "uint", "maximum": "255", "value": "37"}}
            ]
        })
    );
    assert_eq!(
        returns["absentUIntOption"],
        json!({
            "kind": "struct",
            "id": "scalarMaybeAuthoring.MaybeUInt8",
            "fields": [
                {"name": "is_some", "value": {"kind": "bool", "value": false}},
                {"name": "value", "value": {"kind": "uint", "maximum": "255", "value": "0"}}
            ]
        })
    );
    assert_eq!(
        returns["presentBoolOption"],
        json!({
            "kind": "struct",
            "id": "scalarMaybeAuthoring.MaybeBool",
            "fields": [
                {"name": "is_some", "value": {"kind": "bool", "value": true}},
                {"name": "value", "value": {"kind": "bool", "value": true}}
            ]
        })
    );
    assert_eq!(
        returns["absentBoolOption"],
        json!({
            "kind": "struct",
            "id": "scalarMaybeAuthoring.MaybeBool",
            "fields": [
                {"name": "is_some", "value": {"kind": "bool", "value": false}},
                {"name": "value", "value": {"kind": "bool", "value": false}}
            ]
        })
    );
    assert_eq!(
        returns["presentNativeOption"],
        json!({
            "kind": "struct",
            "id": "scalarMaybeAuthoring.MaybeNative",
            "fields": [
                {"name": "is_some", "value": {"kind": "bool", "value": true}},
                {"name": "value", "value": {"kind": "native", "value": "17"}}
            ]
        })
    );
    assert_eq!(
        returns["absentNativeOption"],
        json!({
            "kind": "struct",
            "id": "scalarMaybeAuthoring.MaybeNative",
            "fields": [
                {"name": "is_some", "value": {"kind": "bool", "value": false}},
                {"name": "value", "value": {"kind": "native", "value": "0"}}
            ]
        })
    );
    assert_eq!(
        execution
            .returns()
            .iter()
            .map(|(_, value)| value.clone())
            .collect::<Vec<_>>(),
        [
            Value::Native(Fr::from(1u8)),
            Value::Native(Fr::from(37u8)),
            Value::Native(Fr::from(0u8)),
            Value::Native(Fr::from(0u8)),
            Value::Native(Fr::from(1u8)),
            Value::Native(Fr::from(1u8)),
            Value::Native(Fr::from(0u8)),
            Value::Native(Fr::from(0u8)),
            Value::Native(Fr::from(1u8)),
            Value::Native(Fr::from(17u8)),
            Value::Native(Fr::from(0u8)),
            Value::Native(Fr::from(0u8)),
        ]
    );
    Ok(())
}
