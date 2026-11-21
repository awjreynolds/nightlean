#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use noctium_runtime::{MODULUS, Plan, check, create_state, prepare, zkir::IrSource};
use num_bigint::BigUint;
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};

#[test]
#[ignore = "requires freshly emitted hash conversion artifacts"]
fn hash_domain_conversions_match_compact_boundaries() -> anyhow::Result<()> {
    let artifacts = PathBuf::from(
        std::env::var_os("NOCTIUM_HASH_DOMAIN_CONVERSIONS_DIR")
            .expect("set the fresh hash conversion artifact directory"),
    );
    let plan: Plan = serde_json::from_reader(File::open(
        artifacts.join("HashDomainConversions.inspect.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        artifacts.join("HashDomainConversions.inspect.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let modulus: BigUint = MODULUS.parse()?;
    let truncated = BigUint::from_bytes_le(&[255; 31]).to_string();
    let inputs = |high_byte, field: &BigUint| {
        let mut digest = [255u8; 32];
        digest[31] = high_byte;
        BTreeMap::from([
            ("digest".into(), json!({"kind":"bytes", "values":digest})),
            ("field".into(), json!(field.to_string())),
        ])
    };

    for (high_byte, field) in [(0, BigUint::from(0u8)), (255, &modulus - 1u8)] {
        let execution = prepare(
            &plan,
            &inputs(high_byte, &field),
            &state,
            params,
            ContractAddress::default(),
        )?;
        check(&execution, &circuit)?;
        let mut encoded = field.to_bytes_le();
        encoded.resize(32, 0);
        encoded[31] = 0;
        assert_eq!(execution.returns_json()["truncated"], json!(truncated));
        assert_eq!(
            execution.returns_json()["encoded"],
            json!({"kind":"bytes", "values":encoded})
        );
    }

    assert!(
        prepare(
            &plan,
            &inputs(255, &modulus),
            &state,
            params,
            ContractAddress::default(),
        )
        .is_err()
    );
    Ok(())
}
