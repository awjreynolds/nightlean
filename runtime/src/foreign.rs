//! Checked native codecs for the supported Secp256k1 and Secp256r1 values.

use crate::zkir::{
    ir_instructions::encode::{decode_offcircuit, encode_offcircuit},
    ir_types::{IrType, IrValue},
};
use anyhow::{Result, ensure};
use transient_crypto::curve::Fr;

/// A supported foreign curve family.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForeignFamily {
    Secp256k1,
    Secp256r1,
}

/// A role within a foreign curve family.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ForeignRole {
    Base,
    Scalar,
    Point,
}

/// A closed foreign family and role pair.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ForeignType {
    family: ForeignFamily,
    role: ForeignRole,
}

impl ForeignType {
    pub const fn new(family: ForeignFamily, role: ForeignRole) -> Self {
        Self { family, role }
    }

    pub const fn family(self) -> ForeignFamily {
        self.family
    }

    pub const fn role(self) -> ForeignRole {
        self.role
    }

    pub fn native_type(self) -> IrType {
        match (self.family, self.role) {
            (ForeignFamily::Secp256k1, ForeignRole::Base) => IrType::Secp256k1Base,
            (ForeignFamily::Secp256k1, ForeignRole::Scalar) => IrType::Secp256k1Scalar,
            (ForeignFamily::Secp256k1, ForeignRole::Point) => IrType::Secp256k1Point,
            (ForeignFamily::Secp256r1, ForeignRole::Base) => IrType::Secp256r1Base,
            (ForeignFamily::Secp256r1, ForeignRole::Scalar) => IrType::Secp256r1Scalar,
            (ForeignFamily::Secp256r1, ForeignRole::Point) => IrType::Secp256r1Point,
        }
    }
}

/// A native value whose foreign type and canonical transport have been checked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ForeignValue {
    ty: ForeignType,
    value: IrValue,
}

impl ForeignValue {
    /// Decode the exact canonical native-field encoding for `ty`.
    pub fn decode(ty: ForeignType, encoded: &[Fr]) -> Result<Self> {
        let native_type = ty.native_type();
        ensure!(
            encoded.len() == native_type.encoded_len(),
            "wrong native field count for {native_type:?}"
        );
        let value = decode_offcircuit(encoded, &native_type)?;
        ensure!(
            value_matches_type(&value, ty),
            "native decoder returned the wrong foreign type"
        );
        Ok(Self { ty, value })
    }

    pub const fn foreign_type(&self) -> ForeignType {
        self.ty
    }

    pub fn native_type(&self) -> IrType {
        self.ty.native_type()
    }

    /// Encode with the pinned native codec, preserving its canonical limb rules.
    pub fn encode(&self) -> Result<Vec<Fr>> {
        ensure!(
            value_matches_type(&self.value, self.ty),
            "foreign value does not match its declared type"
        );
        let encoded = encode_offcircuit(&self.value);
        ensure!(
            encoded.len() == self.ty.native_type().encoded_len(),
            "native encoder returned the wrong field count"
        );
        encoded
            .into_iter()
            .map(|field| match field {
                IrValue::Native(value) => Ok(value),
                _ => anyhow::bail!("native encoder returned a non-native field"),
            })
            .collect()
    }
}

fn value_matches_type(value: &IrValue, ty: ForeignType) -> bool {
    matches!(
        (ty.family, ty.role, value),
        (
            ForeignFamily::Secp256k1,
            ForeignRole::Base,
            IrValue::Secp256k1Base(_)
        ) | (
            ForeignFamily::Secp256k1,
            ForeignRole::Scalar,
            IrValue::Secp256k1Scalar(_)
        ) | (
            ForeignFamily::Secp256k1,
            ForeignRole::Point,
            IrValue::Secp256k1Point(_)
        ) | (
            ForeignFamily::Secp256r1,
            ForeignRole::Base,
            IrValue::Secp256r1Base(_)
        ) | (
            ForeignFamily::Secp256r1,
            ForeignRole::Scalar,
            IrValue::Secp256r1Scalar(_)
        ) | (
            ForeignFamily::Secp256r1,
            ForeignRole::Point,
            IrValue::Secp256r1Point(_)
        )
    )
}
