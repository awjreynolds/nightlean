#![cfg(feature = "zkir-321")]

use anyhow::Context;
use noctium_runtime::{check, create_state, prepare, zkir::IrSource, Plan};
use serde_json::{json, Value as Json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_FLAT_FAB_TUPLE_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_FLAT_FAB_TUPLE_DIR")
}

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn inputs(counter: u16, persistent_opening: u8, transient_opening: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("octets".into(), bytes(&(1u8..=32).collect::<Vec<_>>())),
        ("flag".into(), json!(true)),
        ("counterInput".into(), json!(counter.to_string())),
        ("persistentOpening".into(), bytes(&[persistent_opening; 32])),
        (
            "transientOpening".into(),
            json!(transient_opening.to_string()),
        ),
        ("anchor".into(), json!("42")),
    ])
}

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_FLAT_FAB_TUPLE_DIR"]
fn flat_fab_tuple_matches_compact_and_native_relation() -> anyhow::Result<()> {
    let directory = artifacts();
    let plan: Plan =
        serde_json::from_reader(File::open(directory.join("FlatFabTuple.hash.impact.json"))?)?;
    let circuit = IrSource::load(File::open(directory.join("FlatFabTuple.hash.zkir"))?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let cases = [
        (
            257,
            9,
            77,
            "05743c725c44c8d77bf1b9601385ef901ec4040ecb770014a535ddcb5e2840d9",
            "cff69459a493e86a1276354b70bcb77aaac2edaaac6802fda770a68723f3d68d",
            "26379122738253202444518886441389591496658820157546698964272146379194073575416",
        ),
        (
            258,
            9,
            77,
            "4376a00dd2129c85219a8aecd9a8209cad4fdc8d333ed7e127f71220697490c2",
            "c24011e4183df55510160926607b3dc3bcae795f70b69db0e370e9bf9669ccdc",
            "52175680914820761057797808711717819206214043408631344658262904895711887709638",
        ),
        (
            257,
            10,
            77,
            "05743c725c44c8d77bf1b9601385ef901ec4040ecb770014a535ddcb5e2840d9",
            "34f5becb77595f7a8e7eda241d9c187f87e97e5c4af68a14577b668c519030fe",
            "26379122738253202444518886441389591496658820157546698964272146379194073575416",
        ),
        (
            257,
            9,
            78,
            "05743c725c44c8d77bf1b9601385ef901ec4040ecb770014a535ddcb5e2840d9",
            "cff69459a493e86a1276354b70bcb77aaac2edaaac6802fda770a68723f3d68d",
            "1245246646047273088008560749436502138436832274864845859888856457488273394968",
        ),
    ];

    for (
        counter,
        persistent_opening,
        transient_opening,
        expected_hash,
        expected_persistent,
        expected_transient,
    ) in cases
    {
        let execution = prepare(
            &plan,
            &inputs(counter, persistent_opening, transient_opening),
            &initial,
            parameters,
            address,
        )
        .with_context(|| {
            format!(
                "prepare flat FAB tuple with counter {counter}, persistent opening {persistent_opening}, transient opening {transient_opening}"
            )
        })?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        let returns = execution.returns_json();
        assert_eq!(
            returns.get("hashResult"),
            Some(&bytes(&hex::decode(expected_hash)?))
        );
        assert_eq!(
            returns.get("persistentResult"),
            Some(&bytes(&hex::decode(expected_persistent)?))
        );
        assert_eq!(
            returns.get("transientResult"),
            Some(&json!(expected_transient))
        );
    }

    Ok(())
}
