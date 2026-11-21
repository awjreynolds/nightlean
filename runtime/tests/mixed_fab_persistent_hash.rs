#![cfg(feature = "zkir-321")]

use anyhow::Context;
use noctium_runtime::{
    Expr, FabHashInput, Plan, check, create_state, evaluate, prepare, zkir::IrSource,
};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_MIXED_FAB_PERSISTENT_HASH_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_MIXED_FAB_PERSISTENT_HASH_DIR")
}

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn inputs(counter: u16) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("octets".into(), bytes(&(1u8..=32).collect::<Vec<_>>())),
        ("flag".into(), json!(true)),
        ("counterInput".into(), json!(counter.to_string())),
        ("anchor".into(), json!("42")),
    ])
}

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_MIXED_FAB_PERSISTENT_HASH_DIR"]
fn mixed_fab_persistent_hash_matches_compact_and_native_relation() -> anyhow::Result<()> {
    let directory = artifacts();
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("MixedFabPersistentHash.hash.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("MixedFabPersistentHash.hash.zkir"),
    )?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let vectors = [
        (
            257,
            "05743c725c44c8d77bf1b9601385ef901ec4040ecb770014a535ddcb5e2840d9",
        ),
        (
            258,
            "4376a00dd2129c85219a8aecd9a8209cad4fdc8d333ed7e127f71220697490c2",
        ),
    ];

    let output_expression = plan
        .circuit
        .outputs
        .iter()
        .find(|output| output.name == "digest")
        .expect("digest circuit output")
        .expression
        .clone();
    let Expr::PersistentHashFab { schema, mut values } = output_expression else {
        anyhow::bail!("digest output is not a FAB persistent hash")
    };
    let FabHashInput::Bytes { length, .. } = &mut values[0] else {
        anyhow::bail!("first FAB value is not Bytes")
    };
    *length = 31;
    let malformed = Expr::PersistentHashFab { schema, values };
    let error = evaluate(&malformed, &BTreeMap::new()).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("FAB byte field length differs from schema")
    );

    for (counter, expected) in vectors {
        let execution = prepare(&plan, &inputs(counter), &initial, parameters, address)
            .with_context(|| format!("prepare FAB hash with counter {counter}"))?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        let expected = hex::decode(expected)?;
        assert_eq!(
            execution.returns_json().get("resultHash"),
            Some(&bytes(&expected))
        );
    }
    Ok(())
}
