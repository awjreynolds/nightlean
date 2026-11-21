#![cfg(feature = "zkir-321")]

use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use noctium_runtime::{
    Plan, Value, check, create_state,
    foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue},
    prepare,
    zkir::IrSource,
};
use serde_json::{Value as Json, json};
use sha3::{Digest, Keccak256};
use std::collections::BTreeMap;

const GENERATOR: &str = "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
const EXPECTED: &str = "571cf838e63c171196cd7a301bb8fab87d13d946769a41e1004d9da49f6bfca8";

#[test]
fn typed_secp256k1_keccak_matches_compact_fab_encoding_and_binds_output() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/typed-point-keccak/321/TypedPointKeccak.hash.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/typed-point-keccak/321/TypedPointKeccak.hash.zkir").as_slice(),
    )
    .unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let point_type = ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Point);
    let point = ForeignValue::from_bytes(point_type, &hex::decode(GENERATOR).unwrap()).unwrap();
    let inputs = BTreeMap::from([("point".into(), Value::Foreign(point).public_json())]);
    let mut execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).unwrap();

    let compact_encoding = format!(
        "{}{}{}",
        "9717f8165b81f259d928ce2ddbfc9b02070b87ce9562a055acbbdcf97e66be79",
        "b7d410fb8fd0479c195485a648b417fda808110efcfba45d65c4a32677da3a48",
        "00".repeat(32),
    );
    let expected = hex::decode(EXPECTED).unwrap();
    assert_eq!(compact_encoding.len(), 192);
    assert_eq!(
        hex::encode(Keccak256::digest(hex::decode(compact_encoding).unwrap())),
        EXPECTED
    );
    assert_eq!(
        execution.returns(),
        [("pointHashResult".to_owned(), Value::Bytes(expected.clone()))]
    );

    let mut changed_digest = expected.clone();
    changed_digest[0] ^= 1;
    let output = AlignedValue {
        value: FabValue(vec![ValueAtom::from(changed_digest.as_slice())]),
        alignment: Alignment::singleton(AlignmentAtom::Bytes { length: 32 }),
    };
    let (commitment, randomness) = execution.preimage.communications_commitment.unwrap();
    execution.preimage.communications_commitment = Some((
        onchain_runtime::communication_commitment(
            AlignedValue::concat(std::iter::empty::<&AlignedValue>()),
            output,
            randomness,
        ),
        randomness,
    ));
    assert!(execution.preimage.communications_commitment.unwrap().0 != commitment);
    assert!(execution.preimage.check(&circuit).is_err());
    assert!(check(&execution, &circuit).is_err());

    let mut invalid = inputs;
    let Json::Object(point) = invalid.get_mut("point").unwrap() else {
        panic!("expected typed point object");
    };
    let mut invalid_encoding = vec![2u8];
    invalid_encoding.extend([u8::MAX; 32]);
    point.insert("bytes".into(), json!(invalid_encoding));
    assert!(
        prepare(
            &plan,
            &invalid,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .is_err()
    );
}
