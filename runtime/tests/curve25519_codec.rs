#![cfg(feature = "zkir-321")]

use noctium_runtime::field_decimal;
use noctium_runtime::foreign::{
    ForeignBinaryOp, ForeignFamily, ForeignRole, ForeignType, ForeignUnaryOp, ForeignValue,
};
use noctium_runtime::zkir::ir_types::IrType;
use num_bigint::BigUint;
use serde_json::{Value as Json, json};

fn le32(value: &BigUint) -> [u8; 32] {
    let bytes = value.to_bytes_le();
    let mut encoded = [0; 32];
    encoded[..bytes.len()].copy_from_slice(&bytes);
    encoded
}

fn decimal(value: &str) -> BigUint {
    BigUint::parse_bytes(value.as_bytes(), 10).unwrap()
}

#[test]
fn curve25519_native_codecs_cover_fields_points_and_checked_boundaries() {
    let vectors: Json =
        serde_json::from_str(include_str!("fixtures/curve25519/321/encoding.json")).unwrap();
    let field_modulus =
        decimal("57896044618658097711785492504343953926634992332820282019728792003956564819949");
    let scalar_modulus =
        decimal("7237005577332262213973186563042994240857116359379907606001950938285454250989");

    for (role, name, native_type, modulus) in [
        (
            ForeignRole::Base,
            "Curve25519Base",
            IrType::Curve25519Base,
            &field_modulus,
        ),
        (
            ForeignRole::Scalar,
            "Curve25519Scalar",
            IrType::Curve25519Scalar,
            &scalar_modulus,
        ),
    ] {
        let ty = ForeignType::new(ForeignFamily::Curve25519, role);
        assert_eq!(ForeignType::parse_source_name(name).unwrap(), ty);
        assert_eq!(ty.source_name(), name);
        assert_eq!(ty.native_type(), native_type);
        assert_eq!(ty.byte_len(), 32);

        let mut values = vec![
            BigUint::from(0u8),
            BigUint::from(1u8),
            modulus - BigUint::from(1u8),
        ];
        if role == ForeignRole::Scalar {
            values.push((BigUint::from(1u8) << 200usize) + BigUint::from(1u8));
        }
        for value in values {
            let bytes = le32(&value);
            let decoded = ForeignValue::from_bytes(ty, &bytes).unwrap();
            let fields = decoded.encode().unwrap();
            assert_eq!(fields.len(), native_type.encoded_len());
            let native_name = match role {
                ForeignRole::Base => "Base<Curve25519>",
                ForeignRole::Scalar => "Scalar<Curve25519>",
                ForeignRole::Point => unreachable!(),
            };
            let row = vectors["fields"]
                .as_array()
                .unwrap()
                .iter()
                .find(|row| row["type"] == native_name && row["value"] == value.to_str_radix(10))
                .unwrap();
            assert_eq!(
                json!(
                    fields
                        .iter()
                        .copied()
                        .map(field_decimal)
                        .collect::<Vec<_>>()
                ),
                row["encoding"]
            );
            assert_eq!(decoded.to_bytes().unwrap(), bytes);
            assert_eq!(ForeignValue::decode(ty, &fields).unwrap(), decoded);
        }
        assert!(ForeignValue::from_bytes(ty, &le32(modulus)).is_err());
        assert_eq!(ForeignValue::zero(ty).unwrap().to_bytes().unwrap(), [0; 32]);
    }

    let point_ty = ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Point);
    assert_eq!(
        ForeignType::parse_source_name("Curve25519Point").unwrap(),
        point_ty
    );
    assert_eq!(point_ty.native_type(), IrType::Curve25519Point);
    assert_eq!(point_ty.byte_len(), 32);

    let mut identity_bytes = [0; 32];
    identity_bytes[0] = 1;
    let identity = ForeignValue::zero(point_ty).unwrap();
    assert_eq!(
        json!(
            identity
                .encode()
                .unwrap()
                .into_iter()
                .map(field_decimal)
                .collect::<Vec<_>>()
        ),
        vectors["identities"][0]["encoding"]
    );
    assert_eq!(identity.to_bytes().unwrap(), identity_bytes);
    let x = identity.unary(ForeignUnaryOp::X).unwrap();
    let y = identity.unary(ForeignUnaryOp::Y).unwrap();
    assert_eq!(x.to_bytes().unwrap(), [0; 32]);
    assert_eq!(y.to_bytes().unwrap(), le32(&BigUint::from(1u8)));
    assert_eq!(
        x.binary(ForeignBinaryOp::FromCoordinates, &y).unwrap(),
        identity
    );

    let mut generator_bytes = [0x66; 32];
    generator_bytes[0] = 0x58;
    let generator = ForeignValue::from_bytes(point_ty, &generator_bytes).unwrap();
    let generator_fields = generator.encode().unwrap();
    assert_eq!(
        json!(
            generator_fields
                .iter()
                .copied()
                .map(field_decimal)
                .collect::<Vec<_>>()
        ),
        vectors["points"][0]["encoding"]
    );
    assert_eq!(generator_fields.len(), 4);
    assert_eq!(
        ForeignValue::decode(point_ty, &generator_fields).unwrap(),
        generator
    );
    assert_eq!(
        generator
            .unary(ForeignUnaryOp::X)
            .unwrap()
            .binary(
                ForeignBinaryOp::FromCoordinates,
                &generator.unary(ForeignUnaryOp::Y).unwrap(),
            )
            .unwrap(),
        generator
    );

    let scalar = ForeignValue::from_bytes(
        ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Scalar),
        &le32(&BigUint::from(1u8)),
    )
    .unwrap();
    assert_eq!(
        scalar.unary(ForeignUnaryOp::MulGenerator).unwrap(),
        generator
    );
    assert_eq!(
        identity.binary(ForeignBinaryOp::EcMul, &scalar).unwrap(),
        identity
    );

    // y = p - 1, x = 0 is a valid Edwards point of order 2, outside the prime subgroup.
    let mut torsion = [0xff; 32];
    torsion[0] = 0xec;
    torsion[31] = 0x7f;
    assert!(ForeignValue::from_bytes(point_ty, &torsion).is_err());

    let mut noncanonical = torsion;
    noncanonical[0] = 0xed;
    assert!(ForeignValue::from_bytes(point_ty, &noncanonical).is_err());

    let curve_base = ForeignValue::from_bytes(
        ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Base),
        &le32(&BigUint::from(1u8)),
    )
    .unwrap();
    let secp_base = ForeignValue::from_bytes(
        ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Base),
        &le32(&BigUint::from(1u8)),
    )
    .unwrap();
    assert!(curve_base.binary(ForeignBinaryOp::Add, &secp_base).is_err());
}
