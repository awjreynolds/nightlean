#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{Plan, Value, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires fresh NativeScalarEitherReturns artifacts in NOCTIUM_SCALAR_EITHER_RETURNS_DIR"]
fn scalar_either_return_zeroes_the_inactive_side() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_SCALAR_EITHER_RETURNS_DIR")?);
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("NativeScalarEitherReturns.canonicalize.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("NativeScalarEitherReturns.canonicalize.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let address = ContractAddress::default();

    for (is_left, expected_left, expected_right) in [(true, 37u64, 0u64), (false, 0, 513)] {
        let inputs = BTreeMap::from([
            ("isLeft".into(), json!(is_left)),
            ("leftValue".into(), json!("37")),
            ("rightValue".into(), json!("513")),
        ]);
        let execution = prepare(&plan, &inputs, &state, &INITIAL_PARAMETERS, address)?;
        check(&execution, &circuit)?;

        assert_eq!(
            execution.returns_json()["result"],
            json!({
                "kind": "struct",
                "id": "NativeScalarEitherReturns.EitherLeftUInt8RightUInt16",
                "fields": [
                    {"name": "is_left", "value": {"kind": "bool", "value": is_left}},
                    {"name": "left", "value": {"kind": "uint", "maximum": "255", "value": expected_left.to_string()}},
                    {"name": "right", "value": {"kind": "uint", "maximum": "65535", "value": expected_right.to_string()}}
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
                Value::Native(Fr::from(u8::from(is_left))),
                Value::Native(Fr::from(expected_left)),
                Value::Native(Fr::from(expected_right)),
            ]
        );
    }
    Ok(())
}
