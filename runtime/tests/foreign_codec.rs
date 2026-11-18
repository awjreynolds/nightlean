#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue},
    zkir::{
        ir_instructions::{encode::encode_offcircuit, from_bytes::from_bytes_offcircuit},
        ir_types::{IrType, IrValue},
    },
};
use num_bigint::BigUint;
use serde::Deserialize;
use std::collections::BTreeSet;
use transient_crypto::curve::Fr;

#[derive(Deserialize)]
struct Fixture {
    fields: Vec<FieldFixture>,
    identities: Vec<IdentityFixture>,
}

#[derive(Deserialize)]
struct FieldFixture {
    #[serde(rename = "type")]
    ty: String,
    modulus: String,
    value: String,
    encoding: Vec<String>,
}

#[derive(Deserialize)]
struct IdentityFixture {
    #[serde(rename = "type")]
    ty: String,
    encoding: Vec<String>,
}

fn native_value(ty: &IrType, bytes: &[u8]) -> IrValue {
    from_bytes_offcircuit(ty, bytes).unwrap()
}

fn native_encoding(value: &IrValue) -> Vec<Fr> {
    encode_offcircuit(value)
        .into_iter()
        .map(|field| match field {
            IrValue::Native(field) => field,
            _ => panic!("native encoder returned a non-native field"),
        })
        .collect()
}

fn from_biguint(value: &BigUint) -> Fr {
    let bytes = value.to_bytes_le();
    let mut encoded = [0u8; 32];
    encoded[..bytes.len()].copy_from_slice(&bytes);
    Fr::from_le_bytes(&encoded).unwrap()
}

fn as_biguint(value: Fr) -> BigUint {
    BigUint::from_bytes_le(&value.0.to_bytes_le())
}

fn native_type(name: &str) -> (ForeignType, IrType) {
    match name {
        "Base<Secp256k1>" => (
            ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Base),
            IrType::Secp256k1Base,
        ),
        "Scalar<Secp256k1>" => (
            ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Scalar),
            IrType::Secp256k1Scalar,
        ),
        "Base<Secp256r1>" => (
            ForeignType::new(ForeignFamily::Secp256r1, ForeignRole::Base),
            IrType::Secp256r1Base,
        ),
        "Scalar<Secp256r1>" => (
            ForeignType::new(ForeignFamily::Secp256r1, ForeignRole::Scalar),
            IrType::Secp256r1Scalar,
        ),
        "Point<Secp256k1>" => (
            ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Point),
            IrType::Secp256k1Point,
        ),
        "Point<Secp256r1>" => (
            ForeignType::new(ForeignFamily::Secp256r1, ForeignRole::Point),
            IrType::Secp256r1Point,
        ),
        _ => panic!("unexpected fixture type {name}"),
    }
}

fn decimal_bytes(value: &str) -> Vec<u8> {
    BigUint::parse_bytes(value.as_bytes(), 10)
        .unwrap()
        .to_bytes_le()
}

fn decimal_fields(values: &[String]) -> Vec<Fr> {
    values
        .iter()
        .map(|value| from_biguint(&BigUint::parse_bytes(value.as_bytes(), 10).unwrap()))
        .collect()
}

fn field_types() -> [(ForeignType, IrType); 4] {
    [
        (
            ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Base),
            IrType::Secp256k1Base,
        ),
        (
            ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Scalar),
            IrType::Secp256k1Scalar,
        ),
        (
            ForeignType::new(ForeignFamily::Secp256r1, ForeignRole::Base),
            IrType::Secp256r1Base,
        ),
        (
            ForeignType::new(ForeignFamily::Secp256r1, ForeignRole::Scalar),
            IrType::Secp256r1Scalar,
        ),
    ]
}

#[test]
fn canonical_native_codec_covers_all_six_foreign_types() {
    let fixture: Fixture =
        serde_json::from_str(include_str!("fixtures/foreign-codec/321/encoding.json")).unwrap();

    let mut canonical_fields = Vec::new();
    for (ty, native_type) in field_types() {
        for byte in [0u8, 1] {
            let native = native_value(&native_type, &[byte]);
            let encoded = native_encoding(&native);
            let value = ForeignValue::decode(ty, &encoded).unwrap();
            assert_eq!(value.foreign_type(), ty);
            assert_eq!(value.native_type(), native_type);
            assert_eq!(value.encode().unwrap(), encoded);
            canonical_fields.push((ty, native_type.clone(), encoded));
        }
    }

    assert_eq!(fixture.fields.len(), 12);
    assert_eq!(fixture.identities.len(), 2);
    for field in &fixture.fields {
        let (ty, native_type) = native_type(&field.ty);
        let modulus = BigUint::parse_bytes(field.modulus.as_bytes(), 10).unwrap();
        let value = BigUint::parse_bytes(field.value.as_bytes(), 10).unwrap();
        assert!(value < modulus);
        let native = native_value(&native_type, &decimal_bytes(&field.value));
        let native_encoding = native_encoding(&native);
        let lean_encoding = decimal_fields(&field.encoding);
        assert_eq!(
            native_encoding, lean_encoding,
            "{} value {}",
            field.ty, field.value
        );
        assert_eq!(
            ForeignValue::decode(ty, &lean_encoding)
                .unwrap()
                .encode()
                .unwrap(),
            lean_encoding
        );
    }
    for name in [
        "Base<Secp256k1>",
        "Scalar<Secp256k1>",
        "Base<Secp256r1>",
        "Scalar<Secp256r1>",
    ] {
        let entries: Vec<_> = fixture
            .fields
            .iter()
            .filter(|field| field.ty == name)
            .collect();
        let modulus = BigUint::parse_bytes(entries[0].modulus.as_bytes(), 10).unwrap();
        let values: BTreeSet<_> = entries.iter().map(|field| field.value.clone()).collect();
        let expected = BTreeSet::from([
            "0".to_owned(),
            "1".to_owned(),
            (modulus - BigUint::from(1u8)).to_str_radix(10),
        ]);
        assert_eq!(values, expected, "fixture values for {name}");
    }

    for name in ["Point<Secp256k1>", "Point<Secp256r1>"] {
        let fixture_identity = fixture
            .identities
            .iter()
            .find(|identity| identity.ty == name)
            .unwrap();
        let (_, point_type) = native_type(name);
        let native_identity = native_value(&point_type, &[0u8; 33]);
        let native_encoding = native_encoding(&native_identity);
        let lean_encoding = decimal_fields(&fixture_identity.encoding);
        assert_eq!(native_encoding, lean_encoding, "{name}");
    }

    for (family, ty, native_type, generator) in [
        (
            ForeignFamily::Secp256k1,
            ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Point),
            IrType::Secp256k1Point,
            hex::decode("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
                .unwrap(),
        ),
        (
            ForeignFamily::Secp256r1,
            ForeignType::new(ForeignFamily::Secp256r1, ForeignRole::Point),
            IrType::Secp256r1Point,
            hex::decode("036b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296")
                .unwrap(),
        ),
    ] {
        let native_generator = native_value(&native_type, &generator);
        let generator_encoding = native_encoding(&native_generator);
        let generator_value = ForeignValue::decode(ty, &generator_encoding).unwrap();
        assert_eq!(generator_value.foreign_type().family(), family);
        assert_eq!(generator_value.encode().unwrap(), generator_encoding);

        let native_identity = native_value(&native_type, &[0u8; 33]);
        let identity_encoding = native_encoding(&native_identity);
        assert!(
            identity_encoding[..4]
                .iter()
                .all(|limb| *limb != Fr::from(0u64))
        );
        let identity = ForeignValue::decode(ty, &identity_encoding).unwrap();
        assert_eq!(identity.encode().unwrap(), identity_encoding);

        for encoded in [&generator_encoding, &identity_encoding] {
            for invalid in [encoded[..encoded.len() - 1].to_vec(), {
                let mut longer = encoded.clone();
                longer.push(Fr::from(0u64));
                longer
            }] {
                assert!(ForeignValue::decode(ty, &invalid).is_err());
            }
        }

        let mut altered_identity_flag = generator_encoding.clone();
        altered_identity_flag[4] = Fr::from(1u64);
        assert!(ForeignValue::decode(ty, &altered_identity_flag).is_err());

        let mut altered_identity_coordinates = identity_encoding.clone();
        altered_identity_coordinates[0] = Fr::from(0u64);
        assert!(ForeignValue::decode(ty, &altered_identity_coordinates).is_err());

        let mut off_curve = generator_encoding.clone();
        off_curve[0] = off_curve[0] + Fr::from(1u64);
        assert!(ForeignValue::decode(ty, &off_curve).is_err());
    }

    for (ty, native_type, encoded) in &canonical_fields {
        assert!(ForeignValue::decode(*ty, &encoded[..encoded.len() - 1]).is_err());
        assert!(
            ForeignValue::decode(*ty, &[encoded.as_slice(), &[Fr::from(0u64)]].concat()).is_err()
        );

        let mut oversized_low = encoded.clone();
        oversized_low[0] = from_biguint(&(BigUint::from(1u8) << 192));
        assert!(ForeignValue::decode(*ty, &oversized_low).is_err());

        let mut oversized_high = encoded.clone();
        oversized_high[1] = from_biguint(&(BigUint::from(1u8) << 64));
        assert!(ForeignValue::decode(*ty, &oversized_high).is_err());

        let mut alternate_limbs = native_encoding(&native_value(native_type, &[0u8]));
        let low = as_biguint(alternate_limbs[0].clone());
        let high = as_biguint(alternate_limbs[1].clone());
        assert!(high > BigUint::from(0u8));
        alternate_limbs[0] = from_biguint(&(low + (BigUint::from(1u8) << 192)));
        alternate_limbs[1] = from_biguint(&(high - BigUint::from(1u8)));
        assert!(ForeignValue::decode(*ty, &alternate_limbs).is_err());

        let zero = native_encoding(&native_value(native_type, &[0u8]));
        let packed = as_biguint(zero[0].clone()) + (as_biguint(zero[1].clone()) << 192);
        let noncanonical = packed + BigUint::from(1u8);
        let mask = (BigUint::from(1u8) << 192) - BigUint::from(1u8);
        let modulus_limbs = [
            from_biguint(&(&noncanonical & &mask)),
            from_biguint(&(noncanonical >> 192)),
        ];
        assert!(ForeignValue::decode(*ty, &modulus_limbs).is_err());
    }
}
