#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{MODULUS, Plan, check, create_state, prepare, zkir::IrSource};
use num_bigint::BigUint;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

fn bytes(values: &[u8]) -> Json {
    json!({"kind": "bytes", "values": values})
}

fn little_endian(value: &BigUint, width: usize) -> Vec<u8> {
    let mut bytes = value.to_bytes_le();
    bytes.resize(width, 0);
    bytes
}

#[test]
#[ignore = "requires fresh ScalarSerialization Lean artifacts"]
fn scalar_serialization_matches_pinned_reference_and_native_checks() -> Result<()> {
    let output = PathBuf::from(std::env::var("NOCTIUM_SERIALIZATION_ARTIFACTS")?);
    let plan: Plan = serde_json::from_slice(&fs::read(
        output.join("ScalarSerialization.Codec.transcode.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        output.join("ScalarSerialization.Codec.transcode.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let run = |inputs: &BTreeMap<String, Json>| {
        prepare(
            &plan,
            inputs,
            &state,
            &INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };

    let field_modulus: BigUint = MODULUS.parse()?;
    let secp256k1_order: BigUint =
        "115792089237316195423570985008687907852837564279074904382605163141518161494337".parse()?;
    let expected_field = little_endian(&(&field_modulus - 1u8), 34);
    let expected_scalar = little_endian(&(&secp256k1_order - 1u8), 32);
    let mut field_frame = expected_field.clone();
    field_frame[32..].copy_from_slice(&[42, 156]);
    let inputs = BTreeMap::from([
        ("flagFrame".into(), bytes(&[1, 91, 255])),
        ("countFrame".into(), bytes(&[44, 1, 255])),
        ("fieldFrame".into(), bytes(&field_frame)),
        ("scalarFrame".into(), bytes(&expected_scalar)),
        ("byteFrame".into(), bytes(&[12, 42, 255])),
    ]);
    let valid = run(&inputs)?;
    check(&valid, &circuit)?;
    assert_eq!(
        valid.returns_json(),
        BTreeMap::from([
            ("flagEncoding".into(), bytes(&[1, 0, 0])),
            ("countEncoding".into(), bytes(&[44, 1, 0, 0])),
            ("fieldEncoding".into(), bytes(&expected_field)),
            ("scalarEncoding".into(), bytes(&expected_scalar)),
            ("bytesEncoding".into(), bytes(&[12, 42, 0, 0, 0])),
        ])
    );
    let noncanonical = little_endian(&field_modulus, 34);
    for (name, input) in [
        ("flagFrame", bytes(&[2, 0, 0])),
        ("countFrame", bytes(&[45, 1, 0])),
        ("fieldFrame", bytes(&noncanonical)),
    ] {
        let mut invalid = inputs.clone();
        invalid.insert(name.into(), input);
        assert!(run(&invalid).is_err(), "{name}");
    }

    // Compact reduces foreign-field encodings modulo their own field.
    let mut zero = inputs;
    zero.insert("fieldFrame".into(), bytes(&[0; 34]));
    zero.insert(
        "scalarFrame".into(),
        bytes(&little_endian(&secp256k1_order, 32)),
    );
    let mut execution = run(&zero)?;
    check(&execution, &circuit)?;
    let returns = execution.returns_json();
    assert_eq!(returns["scalarEncoding"], bytes(&[0; 32]));
    assert_eq!(returns["fieldEncoding"], bytes(&[0; 34]));

    // Change only the private Native frame, keeping the same residue and public bytes.
    execution.preimage.private_transcript[6..40].copy_from_slice(
        &noncanonical
            .iter()
            .map(|byte| Fr::from(*byte as u64))
            .collect::<Vec<_>>(),
    );
    assert!(check(&execution, &circuit).is_err());
    Ok(())
}
