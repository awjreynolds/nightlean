#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Plan, Value, check, field_decimal, prepare,
    constructor::construct_state,
    foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue},
    zkir::IrSource,
};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, path::PathBuf};
use transient_crypto::curve::Fr;

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_FOREIGN_POINT_ARTIFACTS")
        .map(PathBuf::from)
        .expect("set NOCTIUM_FOREIGN_POINT_ARTIFACTS to fresh compiler outputs")
}

fn point_bytes(family: ForeignFamily) -> Vec<u8> {
    match family {
        ForeignFamily::Secp256k1 => hex::decode(
            "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
        )
        .unwrap(),
        ForeignFamily::Secp256r1 => hex::decode(
            "036b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
        )
        .unwrap(),
        ForeignFamily::Curve25519 => {
            let mut bytes = vec![0x66; 32];
            bytes[0] = 0x58;
            bytes
        }
    }
}

fn field_immediate(value: Fr) -> String {
    let bytes = value.as_le_bytes();
    let width = bytes.iter().rposition(|byte| *byte != 0).map_or(1, |index| index + 1);
    format!("0x{}", hex::encode(&bytes[..width]))
}

fn assert_native_constant(ir: &Json, ty: ForeignType, point: &ForeignValue) {
    let expected: Vec<String> = point
        .encode()
        .unwrap()
        .into_iter()
        .map(field_immediate)
        .collect();
    let type_name = format!("Point<{:?}>", ty.family());
    let constants: Vec<_> = ir["instructions"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|instruction| {
            instruction["op"] == "load_constant" && instruction["type"] == type_name
        })
        .collect();
    assert_eq!(constants.len(), 1, "expected one typed {type_name} constant");
    assert_eq!(constants[0]["encoding"], json!(expected));
}

fn assert_control_constant(control: &Json, ty: ForeignType, point: &ForeignValue) {
    let expected: Vec<String> = point
        .encode()
        .unwrap()
        .into_iter()
        .map(field_decimal)
        .collect();
    let value = &control["functions"][0]["body"][0]["value"];
    assert_eq!(value["tag"], "foreignConstant");
    assert_eq!(value["type"], ty.source_name());
    assert_eq!(value["encoding"], json!(expected));
}

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_FOREIGN_POINT_ARTIFACTS"]
fn affine_point_literals_match_control_zkir_and_native_results() {
    let directory = artifacts();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    for (entry, family) in [
        ("secp256k1", ForeignFamily::Secp256k1),
        ("secp256r1", ForeignFamily::Secp256r1),
        ("curve25519", ForeignFamily::Curve25519),
    ] {
        let stem = format!("ForeignPointLiterals.{entry}");
        let plan: Plan = serde_json::from_slice(
            &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
        )
        .unwrap();
        let circuit_bytes = std::fs::read(directory.join(format!("{stem}.zkir"))).unwrap();
        let ir: Json = serde_json::from_slice(&circuit_bytes).unwrap();
        let circuit = IrSource::load(circuit_bytes.as_slice()).unwrap();
        let ty = ForeignType::new(family, ForeignRole::Point);
        let point = ForeignValue::from_bytes(ty, &point_bytes(family)).unwrap();

        assert_native_constant(&ir, ty, &point);
        if entry == "secp256k1" {
            let control: Json = serde_json::from_slice(
                &std::fs::read(directory.join(format!("{stem}.witness.control.json"))).unwrap(),
            )
            .unwrap();
            assert_control_constant(&control, ty, &point);
        }

        let initial = construct_state(&plan, &BTreeMap::new()).unwrap();
        let execution = prepare(
            &plan,
            &BTreeMap::new(),
            &initial,
            parameters,
            address,
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([("point".into(), Value::Foreign(point).public_json())]),
            "native output for {entry} must preserve the typed affine point"
        );
    }
}
