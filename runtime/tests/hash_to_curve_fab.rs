#![cfg(feature = "zkir-321")]

use anyhow::Context;
use noctium_runtime::{
    Expr, FabHashInput, Plan, check, create_state, evaluate, prepare, zkir::IrSource,
};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::curve::Fr;

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_HASH_TO_CURVE_FAB_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_HASH_TO_CURVE_FAB_DIR")
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
#[ignore = "requires fresh compiler outputs in NOCTIUM_HASH_TO_CURVE_FAB_DIR"]
fn hash_to_curve_fab_matches_compact_and_native_relation() -> anyhow::Result<()> {
    let directory = artifacts();
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("MixedFabHashToCurve.hash.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(directory.join("MixedFabHashToCurve.hash.zkir"))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    let output_expression = plan
        .circuit
        .outputs
        .iter()
        .find(|output| output.name == "resultPoint")
        .context("resultPoint circuit output")?
        .expression
        .clone();
    let Expr::HashToCurveFab { schema, mut values } = output_expression else {
        anyhow::bail!("resultPoint output is not a FAB hash-to-curve expression")
    };
    let FabHashInput::Bytes { length, .. } = &mut values[0] else {
        anyhow::bail!("first FAB value is not Bytes")
    };
    *length = 31;
    let malformed = Expr::HashToCurveFab { schema, values };
    let error = evaluate(&malformed, &BTreeMap::new()).unwrap_err();
    assert!(
        error
            .to_string()
            .contains("FAB byte field length differs from schema")
    );

    let vectors = [
        (
            257,
            json!({
                "kind":"jubjubPoint",
                "x":"28795585433567012869963935944812663991492396026676757706215428925031281335525",
                "y":"22332899933082389804809036260506171817896244000051913394706757537977492146276"
            }),
        ),
        (
            258,
            json!({
                "kind":"jubjubPoint",
                "x":"29703381369117037955354524975024459739721474734473359661960630795432392269544",
                "y":"27301738739419332019240484823733146733474981258073086105370655572681570990521"
            }),
        ),
    ];

    for (counter, expected_point) in vectors {
        let mut execution = prepare(&plan, &inputs(counter), &initial, parameters, address)
            .with_context(|| format!("prepare FAB hash-to-curve with counter {counter}"))?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        assert_eq!(
            execution.returns_json().get("pointResult"),
            Some(&expected_point)
        );

        execution.preimage.private_transcript[3] =
            Fr::from(if counter == 257 { 258u64 } else { 257u64 });
        assert!(check(&execution, &circuit).is_err());
    }
    Ok(())
}
