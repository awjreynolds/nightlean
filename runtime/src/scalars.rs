//! ScalarPolicy.lean-compatible unsigned bounds and checked conversions.
use crate::{MODULUS, Value, canonical_field};
use anyhow::{Result, anyhow, bail, ensure};
use num_bigint::BigUint;

pub const MAX_UINT_BITS: usize = 248;
pub fn max_uint() -> BigUint {
    (BigUint::from(1u8) << MAX_UINT_BITS) - 1u8
}

fn decimal(text: &str) -> Result<BigUint> {
    ensure!(
        !text.is_empty()
            && text.len() <= MODULUS.len()
            && text.bytes().all(|b| b.is_ascii_digit())
            && (text == "0" || !text.starts_with('0')),
        "expected canonical unsigned decimal string"
    );
    BigUint::parse_bytes(text.as_bytes(), 10).ok_or_else(|| anyhow!("invalid unsigned decimal"))
}
pub fn canonical_unsigned(text: &str, maximum: &BigUint) -> Result<BigUint> {
    ensure!(
        *maximum <= max_uint(),
        "unsigned type exceeds target maximum"
    );
    let value = decimal(text)?;
    ensure!(value <= *maximum, "unsigned value outside declared type");
    Ok(value)
}
fn maximum(text: &str) -> Result<BigUint> {
    let value = decimal(text)?;
    ensure!(value <= max_uint(), "unsigned type exceeds target maximum");
    Ok(value)
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ScalarType {
    Native,
    Bool,
    UInt(BigUint),
    Bytes32,
}
impl ScalarType {
    pub fn parse(text: &str) -> Result<Self> {
        match text {
            "Native" => Ok(Self::Native),
            "Bool" => Ok(Self::Bool),
            "Bytes<32>" => Ok(Self::Bytes32),
            _ => {
                let bound = text
                    .strip_prefix("UIntRange<")
                    .and_then(|s| s.strip_suffix('>'))
                    .ok_or_else(|| anyhow!("unsupported scalar type"))?;
                let exclusive = decimal(bound)?;
                ensure!(
                    exclusive > BigUint::from(0u8) && exclusive <= max_uint() + 1u8,
                    "unsigned exclusive bound outside target range"
                );
                Ok(Self::UInt(exclusive - 1u8))
            }
        }
    }
    fn validate(&self) -> Result<()> {
        if let Self::UInt(maximum) = self {
            ensure!(
                *maximum <= max_uint(),
                "unsigned type exceeds target maximum"
            );
        }
        Ok(())
    }
}
impl Value {
    pub fn scalar_type(&self) -> ScalarType {
        match self {
            Self::Native(_) => ScalarType::Native,
            Self::Bool(_) => ScalarType::Bool,
            Self::UInt { maximum, .. } => ScalarType::UInt(maximum.clone()),
            Self::Bytes(_) => ScalarType::Bytes32,
        }
    }
    pub fn validate(&self) -> Result<()> {
        self.scalar_type().validate()?;
        if let Self::UInt { number, maximum } = self {
            ensure!(number <= maximum, "unsigned value outside declared type");
        }
        if let Self::Bytes(bytes) = self {
            ensure!(bytes.len() == 32, "expected 32 bytes");
        }
        Ok(())
    }
    fn number(&self) -> Result<BigUint> {
        Ok(match self {
            Self::Native(n) => BigUint::from_bytes_le(&n.as_le_bytes()),
            Self::Bool(b) => BigUint::from(u8::from(*b)),
            Self::UInt { number, .. } => number.clone(),
            Self::Bytes(_) => bail!("bytes have no numeric scalar encoding"),
        })
    }
    pub fn cast(&self, target: &ScalarType) -> Result<Self> {
        self.validate()?;
        target.validate()?;
        if let Self::Bytes(_) = self {
            ensure!(
                *target == ScalarType::Bytes32,
                "bytes cannot be cast to a scalar"
            );
            return Ok(self.clone());
        }
        let number = self.number()?;
        let result = match target {
            ScalarType::Native => Self::Native(canonical_field(&number.to_str_radix(10))?),
            ScalarType::Bool => Self::Bool(number != BigUint::from(0u8)),
            ScalarType::UInt(maximum) => Self::UInt {
                number,
                maximum: maximum.clone(),
            },
            ScalarType::Bytes32 => bail!("scalars cannot be cast to bytes"),
        };
        result.validate()?;
        Ok(result)
    }
    pub(crate) fn field_encoding(&self) -> Result<transient_crypto::curve::Fr> {
        self.validate()?;
        canonical_field(&self.number()?.to_str_radix(10))
    }
    pub fn public_json(&self) -> serde_json::Value {
        match self {
            Self::Native(n) => serde_json::Value::String(crate::field_decimal(*n)),
            Self::Bool(b) => serde_json::Value::Bool(*b),
            Self::UInt { number, .. } => serde_json::Value::String(number.to_str_radix(10)),
            Self::Bytes(bytes) => serde_json::json!({"kind":"bytes","values":bytes}),
        }
    }
}
pub(crate) fn unsigned_literal(bound: &str, value: &str) -> Result<Value> {
    let maximum = maximum(bound)?;
    let number = canonical_unsigned(value, &maximum)?;
    Ok(Value::UInt { number, maximum })
}
pub(crate) enum UnsignedOp {
    Add,
    Sub,
    Mul,
}
pub(crate) fn unsigned_arithmetic(
    op: UnsignedOp,
    left: Value,
    right: Value,
    bound: &str,
) -> Result<Value> {
    left.validate()?;
    right.validate()?;
    let (
        Value::UInt {
            number: a,
            maximum: m,
        },
        Value::UInt {
            number: b,
            maximum: n,
        },
    ) = (left, right)
    else {
        bail!("unsigned arithmetic requires unsigned operands")
    };
    let inferred = match op {
        UnsignedOp::Add => &m + &n,
        UnsignedOp::Sub => m,
        UnsignedOp::Mul => &m * &n,
    };
    ensure!(
        inferred <= max_uint(),
        "unsigned result type exceeds target maximum"
    );
    ensure!(
        maximum(bound)? == inferred,
        "unsigned result bound mismatch"
    );
    let number = match op {
        UnsignedOp::Add => a + b,
        UnsignedOp::Mul => a * b,
        UnsignedOp::Sub => {
            ensure!(a >= b, "unsigned subtraction underflow");
            a - b
        }
    };
    let result = Value::UInt {
        number,
        maximum: inferred,
    };
    result.validate()?;
    Ok(result)
}
