#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{Plan, Value, check, create_state, prepare, zkir::IrSource};
use serde_json::json;
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires fresh NativeScalarListMaybe artifacts in NOCTIUM_SCALAR_LIST_MAYBE_DIR"]
fn list_head_returns_one_typed_maybe() -> Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_SCALAR_LIST_MAYBE_DIR")?);
    let load = |entry: &str| -> Result<(Plan, IrSource)> {
        let name = format!("NativeScalarListMaybe.{entry}");
        Ok((
            serde_json::from_slice(&fs::read(directory.join(format!("{name}.impact.json")))?)?,
            IrSource::load(fs::File::open(directory.join(format!("{name}.zkir")))?)?,
        ))
    };
    let (head, head_circuit) = load("head")?;
    let (push, push_circuit) = load("push")?;
    let empty = create_state(&head, &BTreeMap::from([("values".into(), json!([]))]))?;
    let address = ContractAddress::default();
    let added = prepare(
        &push,
        &BTreeMap::from([("value".into(), json!("37"))]),
        &empty,
        &INITIAL_PARAMETERS,
        address,
    )?;
    check(&added, &push_circuit)?;

    for (state, present, value) in [(&empty, false, 0u64), (&added.after.state, true, 37)] {
        let result = prepare(&head, &BTreeMap::new(), state, &INITIAL_PARAMETERS, address)?;
        check(&result, &head_circuit)?;
        let returns = result.returns_json();
        assert_eq!(returns.len(), 1);
        assert_eq!(returns["head"]["kind"], "struct");
        assert_eq!(
            returns["head"]["fields"],
            json!([
                {"name": "is_some", "value": {"kind": "bool", "value": present}},
                {"name": "value", "value": {"kind": "uint", "maximum": "255", "value": value.to_string()}}
            ])
        );
        assert_eq!(
            result
                .returns()
                .iter()
                .map(|(_, value)| value.clone())
                .collect::<Vec<_>>(),
            [
                Value::Native(Fr::from(u8::from(present))),
                Value::Native(Fr::from(value))
            ]
        );
    }
    Ok(())
}
