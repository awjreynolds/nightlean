#![cfg(feature = "zkir-321")]

use anyhow::Result;
use noctium_runtime::{
    Plan, Value, check,
    constructor::construct_state,
    foreign::{ForeignType, ForeignValue},
    prepare,
    zkir::IrSource,
};
use num_bigint::BigUint;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};

fn artifacts() -> PathBuf {
    PathBuf::from(
        env::var_os("NOCTIUM_FOREIGN_FIELD_NEG_INV_DIR")
            .expect("set fresh outputs in NOCTIUM_FOREIGN_FIELD_NEG_INV_DIR"),
    )
}

fn modulus(type_name: &str) -> BigUint {
    for fixture in [
        include_str!("fixtures/foreign-codec/321/encoding.json"),
        include_str!("fixtures/curve25519/321/encoding.json"),
    ] {
        let fixture: Json = serde_json::from_str(fixture).unwrap();
        if let Some(row) = fixture["fields"]
            .as_array()
            .and_then(|fields| fields.iter().find(|row| row["type"] == type_name))
        {
            return BigUint::parse_bytes(row["modulus"].as_str().unwrap().as_bytes(), 10).unwrap();
        }
    }
    panic!("missing modulus for {type_name}");
}

fn bytes32(number: &BigUint) -> [u8; 32] {
    let bytes = number.to_bytes_le();
    assert!(bytes.len() <= 32);
    let mut output = [0u8; 32];
    output[..bytes.len()].copy_from_slice(&bytes);
    output
}

fn foreign_json(ty: ForeignType, value: &BigUint) -> Json {
    Value::Foreign(ForeignValue::from_bytes(ty, &bytes32(value)).unwrap()).public_json()
}

#[test]
#[ignore = "requires fresh ForeignFieldNegInv artifacts in NOCTIUM_FOREIGN_FIELD_NEG_INV_DIR"]
fn typed_foreign_field_negation_and_inverse_match_pinned_native_relations() -> Result<()> {
    let directory = artifacts();
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("ForeignFieldNegInv.checkFields.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("ForeignFieldNegInv.checkFields.zkir"),
    )?)?;
    let state = construct_state(&plan, &BTreeMap::new())?;
    let address = coin_structure::contract::ContractAddress::default();
    let fields = [
        (
            "k1Base",
            "k1BaseZero",
            "rejectK1BaseInvZero",
            "k1BaseNeg",
            "k1BaseInv",
            "k1BaseZeroNeg",
            "Base<Secp256k1>",
            "Secp256k1Base",
            5u8,
        ),
        (
            "k1Scalar",
            "k1ScalarZero",
            "rejectK1ScalarInvZero",
            "k1ScalarNeg",
            "k1ScalarInv",
            "k1ScalarZeroNeg",
            "Scalar<Secp256k1>",
            "Secp256k1Scalar",
            7u8,
        ),
        (
            "r1Base",
            "r1BaseZero",
            "rejectR1BaseInvZero",
            "r1BaseNeg",
            "r1BaseInv",
            "r1BaseZeroNeg",
            "Base<Secp256r1>",
            "Secp256r1Base",
            11u8,
        ),
        (
            "r1Scalar",
            "r1ScalarZero",
            "rejectR1ScalarInvZero",
            "r1ScalarNeg",
            "r1ScalarInv",
            "r1ScalarZeroNeg",
            "Scalar<Secp256r1>",
            "Secp256r1Scalar",
            13u8,
        ),
        (
            "c255Base",
            "c255BaseZero",
            "rejectC255BaseInvZero",
            "c255BaseNeg",
            "c255BaseInv",
            "c255BaseZeroNeg",
            "Base<Curve25519>",
            "Curve25519Base",
            17u8,
        ),
        (
            "c255Scalar",
            "c255ScalarZero",
            "rejectC255ScalarInvZero",
            "c255ScalarNeg",
            "c255ScalarInv",
            "c255ScalarZeroNeg",
            "Scalar<Curve25519>",
            "Curve25519Scalar",
            19u8,
        ),
    ];
    let mut inputs = BTreeMap::new();
    let mut expected = BTreeMap::new();
    for (
        value_name,
        zero_name,
        guard_name,
        neg_name,
        inv_name,
        zero_neg_name,
        type_name,
        source_name,
        value,
    ) in fields
    {
        let ty = ForeignType::parse_source_name(source_name)?;
        let number = BigUint::from(value);
        let zero = BigUint::from(0u8);
        let prime = modulus(type_name);
        inputs.insert(value_name.into(), foreign_json(ty, &number));
        inputs.insert(zero_name.into(), foreign_json(ty, &zero));
        inputs.insert(guard_name.into(), json!(false));
        expected.insert(neg_name.into(), foreign_json(ty, &(&prime - &number)));
        expected.insert(
            inv_name.into(),
            foreign_json(ty, &number.modpow(&(&prime - 2u8), &prime)),
        );
        expected.insert(zero_neg_name.into(), foreign_json(ty, &zero));
    }

    let execution = prepare(
        &plan,
        &inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        address,
    )?;
    check(&execution, &circuit)?;
    assert_eq!(execution.returns_json(), expected);
    assert_eq!(execution.after.state.get_ref(), state.get_ref());

    for (_, _, guard_name, _, _, _, _, _, _) in fields {
        let mut zero_inverse = inputs.clone();
        zero_inverse.insert(guard_name.into(), json!(true));
        assert!(
            prepare(
                &plan,
                &zero_inverse,
                &state,
                &ledger::structure::INITIAL_PARAMETERS,
                address,
            )
            .is_err(),
            "zero inverse must reject for {guard_name}"
        );
    }
    Ok(())
}
