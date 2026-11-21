#![cfg(feature = "zkir-321")]

use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde::Deserialize;
use serde_json::Value;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[derive(Deserialize)]
struct Reference {
    inputs: BTreeMap<String, Value>,
    outputs: BTreeMap<String, Value>,
}

#[test]
#[ignore = "requires fresh Lean and Compact outputs in NOCTIUM_SECP_PROJECTIONS_DIR"]
fn native_secp_points_scalars_and_affine_coordinates_match_compact() -> anyhow::Result<()> {
    let directory = PathBuf::from(std::env::var("NOCTIUM_SECP_PROJECTIONS_DIR")?);
    let reference: Reference =
        serde_json::from_reader(File::open(directory.join("compact.json"))?)?;
    let directory = directory.join("lean");
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("SecpProjections.inspect.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(directory.join("SecpProjections.inspect.zkir"))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let execution = prepare(&plan, &reference.inputs, &initial, parameters, address)?;
    check(&execution, &circuit)?;
    assert_eq!(execution.returns_json(), reference.outputs);

    let mut invalid = reference.inputs;
    invalid.insert("kPoint".into(), invalid["rPoint"].clone());
    assert!(prepare(&plan, &invalid, &initial, parameters, address).is_err());
    Ok(())
}
