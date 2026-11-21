#![cfg(feature = "zkir-321")]

use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_INDEXED_SHIELDED_NONCE_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_INDEXED_SHIELDED_NONCE_DIR")
}

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn inputs(index: &str, nonce: &[u8; 32]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("index".into(), json!(index)),
        ("nonce".into(), bytes(nonce)),
    ])
}

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_INDEXED_SHIELDED_NONCE_DIR"]
fn indexed_shielded_nonce_matches_compact_and_discards_the_high_byte() -> anyhow::Result<()> {
    let directory = artifacts();
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("IndexedShieldedNonce.evolve.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("IndexedShieldedNonce.evolve.zkir"),
    )?)?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    const MAX_INDEX: &str = "340282366920938463463374607431768211455";
    let expected_at_zero = bytes(&hex::decode(
        "f2bd6732969e6e5d895070978de9462e7d70a932ac37b21387b1521f207f5300",
    )?);
    let expected_at_maximum = bytes(&hex::decode(
        "0c0163afc8a0a7f18df615e077cfc07cb21784e19a74f23eb48318b51ccb1800",
    )?);
    let mut first_nonce = [0u8; 32];
    for (offset, byte) in first_nonce.iter_mut().enumerate() {
        *byte = u8::try_from(offset + 1)?;
    }
    let mut nonce_with_changed_high_byte = first_nonce;
    nonce_with_changed_high_byte[31] ^= 0xff;

    let cases = [
        ("0", first_nonce, expected_at_zero),
        (MAX_INDEX, first_nonce, expected_at_maximum.clone()),
        (MAX_INDEX, nonce_with_changed_high_byte, expected_at_maximum),
    ];
    for (index, nonce, expected) in cases {
        let execution = prepare(&plan, &inputs(index, &nonce), &initial, parameters, address)?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        assert_eq!(execution.returns_json().get("result"), Some(&expected));
    }
    Ok(())
}
