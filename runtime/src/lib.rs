//! Native execution of the bounded Noctium plan schema. No process or JavaScript API.
use crate::zkir::IrSource;
use anyhow::{Context, Result, anyhow, bail, ensure};
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use base_crypto::repr::BinaryHashRepr;
use coin_structure::contract::ContractAddress;
use ledger::{
    construct::{PreTranscript, partition_transcripts},
    structure::LedgerParameters,
};
use num_bigint::BigUint;
use onchain_runtime::result_mode::{GatherEvent, ResultModeGather};
use onchain_runtime::{
    context::QueryContext,
    ops::{Key, Op},
    result_mode::ResultModeVerify,
    state::{ChargedState, StateValue},
    transcript::Transcript,
};
use serde::Deserialize;
use serde_json::Value as Json;
use sha2::{Digest, Sha256};
use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};
use storage::{arena::Sp, db::InMemoryDB};
use transient_crypto::{
    curve::{EmbeddedFr, EmbeddedGroupAffine, Fr},
    fab::{AlignedValueExt, AlignmentExt, ValueReprAlignedValue},
    hash::transient_hash,
    proofs::{KeyLocation, ProofPreimage},
    repr::FieldRepr,
};

pub const LEDGER_REVISION: &str = "a2b30128ca4b660b73a068e29b56b48ede8c9a74";
pub const ZKIR_REVISION: &str = profile::REVISION;
pub const MODULUS: &str =
    "52435875175126190479447740508185965837690552500527637822603658699938581184513";
pub type Db = InMemoryDB;
pub type Program = Vec<Op<ResultModeVerify, Db>>;

#[derive(Clone, Debug, PartialEq)]
pub enum Value {
    Native(Fr),
    Bool(bool),
    UInt { number: BigUint, maximum: BigUint },
    Bytes(Vec<u8>),
    JubjubScalar(EmbeddedFr),
    JubjubPoint(EmbeddedGroupAffine),
}
impl Value {
    fn field(&self) -> Result<Fr> {
        match self {
            Self::Native(n) => Ok(*n),
            _ => bail!("expected Native value"),
        }
    }
    fn boolean(&self) -> Result<bool> {
        match self {
            Self::Bool(b) => Ok(*b),
            _ => bail!("expected Bool value"),
        }
    }
    fn jubjub_scalar(&self) -> Result<EmbeddedFr> {
        match self {
            Self::JubjubScalar(value) => Ok(*value),
            _ => bail!("expected JubjubScalar value"),
        }
    }
    fn jubjub_point(&self) -> Result<EmbeddedGroupAffine> {
        match self {
            Self::JubjubPoint(value) => Ok(*value),
            _ => bail!("expected JubjubPoint value"),
        }
    }
}
pub fn canonical_field(text: &str) -> Result<Fr> {
    ensure!(
        !text.is_empty()
            && text.len() <= MODULUS.len()
            && text.bytes().all(|b| b.is_ascii_digit())
            && (text == "0" || !text.starts_with('0')),
        "Native input must be a canonical decimal string"
    );
    let n =
        BigUint::parse_bytes(text.as_bytes(), 10).ok_or_else(|| anyhow!("invalid Native input"))?;
    ensure!(
        n < BigUint::parse_bytes(MODULUS.as_bytes(), 10).unwrap(),
        "Native input out of range"
    );
    Fr::from_le_bytes(&n.to_bytes_le()).ok_or_else(|| anyhow!("invalid Native encoding"))
}
pub fn field_decimal(n: Fr) -> String {
    BigUint::from_bytes_le(&n.as_le_bytes()).to_str_radix(10)
}
pub fn field_value(n: Fr) -> AlignedValue {
    AlignedValue {
        value: FabValue(vec![n.into()]),
        alignment: Alignment::singleton(AlignmentAtom::Field),
    }
}
fn aligned(value: &Value, alignment: &str) -> Result<AlignedValue> {
    match alignment {
        "field" => Ok(field_value(value.field_encoding()?)),
        "bit" => Ok(AlignedValue {
            value: FabValue(vec![ValueAtom(if value.boolean()? {
                vec![1]
            } else {
                vec![]
            })]),
            alignment: Alignment::singleton(AlignmentAtom::Bytes { length: 1 }),
        }),
        "bytes32" => {
            let Value::Bytes(bytes) = value else {
                bail!("expected bytes value")
            };
            ensure!(bytes.len() == 32, "expected 32 bytes");
            Ok(AlignedValue {
                value: FabValue(vec![ValueAtom::from(bytes.as_slice())]),
                alignment: Alignment::singleton(AlignmentAtom::Bytes { length: 32 }),
            })
        }
        "u64" => {
            let Value::UInt { number, maximum } = value else {
                bail!("counter alignment requires UInt64")
            };
            ensure!(
                *maximum == BigUint::from(u64::MAX),
                "counter alignment requires UInt64"
            );
            let number =
                u64::try_from(number.clone()).map_err(|_| anyhow!("counter value exceeds u64"))?;
            Ok(number.into())
        }
        _ => bail!("unsupported alignment"),
    }
}
#[derive(Clone, Debug, Deserialize, PartialEq, Eq)]
#[serde(tag = "tag", rename_all = "lowercase", deny_unknown_fields)]
pub enum Expr {
    Constant {
        value: String,
    },
    Bool {
        value: bool,
    },
    Uint {
        maximum: String,
        value: String,
    },
    Uadd {
        left: Box<Expr>,
        right: Box<Expr>,
        maximum: String,
    },
    Usub {
        left: Box<Expr>,
        right: Box<Expr>,
        maximum: String,
    },
    Umul {
        left: Box<Expr>,
        right: Box<Expr>,
        maximum: String,
    },
    Sub {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Inv {
        value: Box<Expr>,
    },
    #[serde(rename = "toBytes32")]
    ToBytes32 {
        value: Box<Expr>,
    },
    #[serde(rename = "fromBytes32")]
    FromBytes32 {
        #[serde(rename = "type")]
        ty: String,
        value: Box<Expr>,
    },
    Cast {
        #[serde(rename = "type")]
        ty: String,
        value: Box<Expr>,
    },
    Reference {
        name: String,
    },
    #[serde(rename = "byteAt")]
    ByteAt {
        value: Box<Expr>,
        index: usize,
    },
    #[serde(rename = "bytesField")]
    BytesField {
        value: Box<Expr>,
        index: usize,
    },
    #[serde(rename = "persistentHash32")]
    PersistentHash32 {
        value: Box<Expr>,
    },
    #[serde(rename = "bytes32Literal")]
    Bytes32Literal {
        values: Vec<u8>,
    },
    #[serde(rename = "persistentHashVector32")]
    PersistentHashVector32 {
        values: Vec<Expr>,
    },
    #[serde(rename = "persistentHashNative")]
    PersistentHashNative {
        value: Box<Expr>,
    },
    #[serde(rename = "persistentHashNativeVector")]
    PersistentHashNativeVector {
        values: Vec<Expr>,
    },
    #[serde(rename = "jubjubScalarFromNative")]
    JubjubScalarFromNative {
        value: Box<Expr>,
    },
    #[serde(rename = "jubjubScalarToNative")]
    JubjubScalarToNative {
        value: Box<Expr>,
    },
    #[serde(rename = "jubjubMulGenerator")]
    JubjubMulGenerator {
        scalar: Box<Expr>,
    },
    #[serde(rename = "jubjubMul")]
    JubjubMul {
        point: Box<Expr>,
        scalar: Box<Expr>,
    },
    #[serde(rename = "jubjubAdd")]
    JubjubAdd {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    #[serde(rename = "jubjubNeg")]
    JubjubNeg {
        point: Box<Expr>,
    },
    #[serde(rename = "jubjubCoordinate")]
    JubjubCoordinate {
        point: Box<Expr>,
        index: usize,
    },
    #[serde(rename = "jubjubFromCoordinates")]
    JubjubFromCoordinates {
        x: Box<Expr>,
        y: Box<Expr>,
    },
    Let {
        name: String,
        value: Box<Expr>,
        body: Box<Expr>,
    },
    #[serde(rename = "assertThen")]
    AssertThen {
        condition: Box<Expr>,
        body: Box<Expr>,
    },
    Add {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Mul {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Eq {
        left: Box<Expr>,
        right: Box<Expr>,
    },
    Select {
        condition: Box<Expr>,
        yes: Box<Expr>,
        no: Box<Expr>,
    },
    Poseidon2 {
        domain: String,
        left: Box<Expr>,
        right: Box<Expr>,
    },
}
pub type Environment = BTreeMap<String, Value>;
fn persistent_hash(value: AlignedValue) -> Result<Value> {
    let mut fields = Vec::new();
    value.value_only_field_repr(&mut fields);
    let decoded = value
        .alignment
        .parse_field_repr(&fields)
        .ok_or_else(|| anyhow!("invalid persistent hash alignment"))?;
    let mut bytes = zeroize::Zeroizing::new(Vec::new());
    ValueReprAlignedValue(decoded).binary_repr(&mut *bytes);
    Ok(Value::Bytes(Sha256::digest(bytes.as_slice()).to_vec()))
}

pub fn evaluate(expr: &Expr, env: &Environment) -> Result<Value> {
    let result = match expr {
        Expr::Uint { maximum, value } => scalars::unsigned_literal(maximum, value)?,
        Expr::Uadd {
            left,
            right,
            maximum,
        } => scalars::unsigned_arithmetic(
            scalars::UnsignedOp::Add,
            evaluate(left, env)?,
            evaluate(right, env)?,
            maximum,
        )?,
        Expr::Usub {
            left,
            right,
            maximum,
        } => scalars::unsigned_arithmetic(
            scalars::UnsignedOp::Sub,
            evaluate(left, env)?,
            evaluate(right, env)?,
            maximum,
        )?,
        Expr::Umul {
            left,
            right,
            maximum,
        } => scalars::unsigned_arithmetic(
            scalars::UnsignedOp::Mul,
            evaluate(left, env)?,
            evaluate(right, env)?,
            maximum,
        )?,
        Expr::Let { name, value, body } => {
            let value = evaluate(value, env)?;
            let mut local = env.clone();
            local.insert(name.clone(), value);
            evaluate(body, &local)?
        }
        Expr::AssertThen { condition, body } => {
            ensure!(
                evaluate(condition, env)?.boolean()?,
                "helper assertion failed"
            );
            evaluate(body, env)?
        }
        Expr::Cast { ty, value } => evaluate(value, env)?.cast(&ScalarType::parse(ty)?)?,
        Expr::Sub { left, right } => {
            Value::Native(evaluate(left, env)?.field()? - evaluate(right, env)?.field()?)
        }
        Expr::Constant { value } => Value::Native(canonical_field(value)?),
        Expr::Bool { value } => Value::Bool(*value),
        Expr::Reference { name } => env
            .get(name)
            .cloned()
            .ok_or_else(|| anyhow!("unbound reference '{name}'"))?,
        Expr::ByteAt { value, index } => {
            let Value::Bytes(bytes) = evaluate(value, env)? else {
                bail!("byte projection requires bytes")
            };
            let byte = bytes
                .get(*index)
                .ok_or_else(|| anyhow!("byte index out of range"))?;
            Value::UInt {
                number: BigUint::from(*byte),
                maximum: BigUint::from(255u16),
            }
        }
        Expr::BytesField { value, index } => {
            let value = aligned(&evaluate(value, env)?, "bytes32")?;
            let mut fields = Vec::new();
            value.value_only_field_repr(&mut fields);
            Value::Native(
                *fields
                    .get(*index)
                    .ok_or_else(|| anyhow!("Bytes32 field index must be 0 or 1"))?,
            )
        }
        Expr::Bytes32Literal { values } => {
            ensure!(
                values.len() == 32,
                "Bytes32 literal must contain exactly 32 bytes"
            );
            Value::Bytes(values.clone())
        }
        Expr::PersistentHash32 { value } => {
            persistent_hash(aligned(&evaluate(value, env)?, "bytes32")?)?
        }
        Expr::PersistentHashVector32 { values } => {
            ensure!(
                (1..=32).contains(&values.len()),
                "persistent hash vector must contain 1 to 32 Bytes32 values"
            );
            let parts = values
                .iter()
                .map(|value| aligned(&evaluate(value, env)?, "bytes32"))
                .collect::<Result<Vec<_>>>()?;
            persistent_hash(AlignedValue::concat(&parts))?
        }
        Expr::PersistentHashNative { value } => {
            persistent_hash(field_value(evaluate(value, env)?.field()?))?
        }
        Expr::PersistentHashNativeVector { values } => {
            ensure!(
                (1..=32).contains(&values.len()),
                "Native persistent hash vector must contain 1 to 32 fields"
            );
            let parts = values
                .iter()
                .map(|value| Ok(field_value(evaluate(value, env)?.field()?)))
                .collect::<Result<Vec<_>>>()?;
            persistent_hash(AlignedValue::concat(&parts))?
        }
        Expr::JubjubScalarFromNative { value } => {
            Value::JubjubScalar(jubjub::reduce_scalar(evaluate(value, env)?.field()?)?)
        }
        Expr::Inv { value } => match evaluate(value, env)? {
            Value::Native(value) => {
                ensure!(value != Fr::from(0u64), "cannot invert zero");
                Value::Native(Fr::from(1u64) / value)
            }
            Value::JubjubScalar(value) => {
                ensure!(value != EmbeddedFr::from(0u64), "cannot invert zero");
                Value::JubjubScalar(EmbeddedFr::from(1u64) / value)
            }
            _ => bail!("inverse requires Native or JubjubScalar"),
        },
        Expr::ToBytes32 { value } => Value::Bytes(match evaluate(value, env)? {
            Value::Native(value) => value.as_le_bytes(),
            Value::JubjubScalar(value) => value.as_le_bytes(),
            Value::JubjubPoint(value) => jubjub::to_bytes(value)?.to_vec(),
            _ => bail!("toBytes32 requires Native, JubjubScalar or JubjubPoint"),
        }),
        Expr::FromBytes32 { ty, value } => {
            let Value::Bytes(bytes) = evaluate(value, env)? else {
                bail!("fromBytes32 requires Bytes32")
            };
            ensure!(bytes.len() == 32, "fromBytes32 requires 32 bytes");
            match ScalarType::parse(ty)? {
                ScalarType::Native => {
                    let number = BigUint::from_bytes_le(&bytes)
                        % BigUint::parse_bytes(MODULUS.as_bytes(), 10).unwrap();
                    Value::Native(
                        Fr::from_le_bytes(&number.to_bytes_le())
                            .ok_or_else(|| anyhow!("invalid reduced Native encoding"))?,
                    )
                }
                ScalarType::JubjubScalar => Value::JubjubScalar(
                    EmbeddedFr::from_le_bytes_wide(&bytes)
                        .ok_or_else(|| anyhow!("invalid reduced Jubjub scalar encoding"))?,
                ),
                ScalarType::JubjubPoint => Value::JubjubPoint(jubjub::from_bytes(&bytes)?),
                _ => bail!("fromBytes32 requires Native, JubjubScalar or JubjubPoint"),
            }
        }
        Expr::JubjubScalarToNative { value } => Value::Native(jubjub::scalar_native(
            evaluate(value, env)?.jubjub_scalar()?,
        )?),
        Expr::JubjubMulGenerator { scalar } => Value::JubjubPoint(
            EmbeddedGroupAffine::generator() * evaluate(scalar, env)?.jubjub_scalar()?,
        ),
        Expr::JubjubMul { point, scalar } => Value::JubjubPoint(
            evaluate(point, env)?.jubjub_point()? * evaluate(scalar, env)?.jubjub_scalar()?,
        ),
        Expr::JubjubAdd { left, right } => Value::JubjubPoint(
            evaluate(left, env)?.jubjub_point()? + evaluate(right, env)?.jubjub_point()?,
        ),
        Expr::JubjubNeg { point } => Value::JubjubPoint(-evaluate(point, env)?.jubjub_point()?),
        Expr::JubjubCoordinate { point, index } => {
            let coordinates = jubjub::coordinates(evaluate(point, env)?.jubjub_point()?)?;
            Value::Native(
                *coordinates
                    .get(*index)
                    .ok_or_else(|| anyhow!("Jubjub coordinate index out of range"))?,
            )
        }
        Expr::JubjubFromCoordinates { x, y } => Value::JubjubPoint(jubjub::point(
            evaluate(x, env)?.field()?,
            evaluate(y, env)?.field()?,
        )?),
        Expr::Add { left, right } => {
            Value::Native(evaluate(left, env)?.field()? + evaluate(right, env)?.field()?)
        }
        Expr::Mul { left, right } => {
            Value::Native(evaluate(left, env)?.field()? * evaluate(right, env)?.field()?)
        }
        Expr::Eq { left, right } => {
            let a = evaluate(left, env)?;
            let b = evaluate(right, env)?;
            ensure!(a.scalar_type() == b.scalar_type(), "equality type mismatch");
            Value::Bool(a == b)
        }
        Expr::Select { condition, yes, no } => {
            let c = evaluate(condition, env)?.boolean()?;
            let a = evaluate(yes, env)?;
            let b = evaluate(no, env)?;
            ensure!(
                a.scalar_type() == b.scalar_type(),
                "selection type mismatch"
            );
            if c { a } else { b }
        }
        Expr::Poseidon2 {
            domain,
            left,
            right,
        } => Value::Native(transient_hash(&[
            canonical_field(domain)?,
            evaluate(left, env)?.field()?,
            evaluate(right, env)?.field()?,
        ])),
    };
    result.validate()?;
    Ok(result)
}
#[derive(Clone, Debug, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct Plan {
    #[serde(default)]
    pub target: Option<String>,
    #[serde(default)]
    pub target_profile: Option<Json>,
    pub schema_version: u32,
    pub entrypoint: String,
    pub circuit: Circuit,
    pub state: Vec<StateDecl>,
    pub operations: Vec<Instruction>,
    pub reads: Vec<Read>,
    #[serde(default)]
    pub returns: Vec<Output>,
}
#[derive(Clone, Debug, Deserialize)]
pub struct Circuit {
    pub inputs: Vec<Input>,
    pub outputs: Vec<Output>,
}
#[derive(Clone, Debug, Deserialize)]
pub struct Input {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub visibility: String,
}
#[derive(Clone, Debug, Deserialize)]
pub struct Output {
    pub visibility: String,
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub expression: Expr,
}
#[derive(Clone, Debug, Deserialize)]
pub struct StateDecl {
    pub name: String,
    pub kind: Json,
}
#[derive(Clone, Debug, Deserialize)]
pub struct Read {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
    #[serde(default)]
    pub guard: Option<Expr>,
    #[serde(default)]
    pub components: Vec<ReadComponent>,
    #[serde(default)]
    pub schema: Option<Json>,
}
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ReadComponent {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
}
#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PathPart {
    pub alignment: String,
    pub expression: Expr,
}
#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "op", rename_all = "lowercase", deny_unknown_fields)]
pub enum Instruction {
    Guarded {
        guard: Expr,
        operation: Box<Instruction>,
    },
    Dup,
    Index {
        slot: u32,
        #[serde(rename = "pushPath")]
        push_path: bool,
        #[serde(default)]
        key: Option<Expr>,
    },
    #[serde(rename = "indexPath")]
    IndexPath {
        slot: u32,
        #[serde(rename = "pushPath")]
        push_path: bool,
        keys: Vec<PathPart>,
    },
    New,
    Push {
        storage: bool,
        expression: Expr,
        alignment: String,
    },
    #[serde(rename = "pushFields")]
    PushFields {
        storage: bool,
        expressions: Vec<Expr>,
        schema: Json,
    },
    Popeq {
        expression: Expr,
        alignment: String,
    },
    #[serde(rename = "popeqFields")]
    PopeqFields {
        expressions: Vec<Expr>,
        schema: Json,
    },
    Member,
    Insert {
        n: u8,
    },
    #[serde(rename = "listLength")]
    ListLength {
        slot: u32,
        keys: Vec<PathPart>,
        expression: Expr,
    },
    #[serde(rename = "listHead")]
    ListHead {
        slot: u32,
        keys: Vec<PathPart>,
        schema: Json,
        expressions: Vec<Expr>,
    },
    #[serde(rename = "listPushFront")]
    ListPushFront {
        slot: u32,
        keys: Vec<PathPart>,
        schema: Json,
        expressions: Vec<Expr>,
    },
    #[serde(rename = "listPopFront")]
    ListPopFront {
        slot: u32,
        keys: Vec<PathPart>,
    },
    #[serde(rename = "listReset")]
    ListReset {
        slot: u32,
        keys: Vec<PathPart>,
    },
    #[serde(rename = "addImmediate")]
    AddImmediate {
        amount: u32,
    },
    #[serde(rename = "subImmediate")]
    SubImmediate {
        amount: u32,
    },
}

fn path_field_count(plan: &Plan, slot: u32, keys: &[PathPart]) -> Result<usize> {
    let types = map_path_key_types(plan, slot, keys.len())?;
    let mut fields = 4;
    for (part, ty) in keys.iter().zip(types) {
        ensure!(
            part.alignment == key_alignment(&ty),
            "map path key alignment mismatch"
        );
        fields += match part.alignment.as_str() {
            "field" | "bit" => 3,
            "bytes32" => 4,
            _ => bail!("unsupported path alignment"),
        };
    }
    Ok(fields)
}

fn impact_field_counts(instruction: &Instruction, plan: &Plan) -> Result<Vec<usize>> {
    Ok(match instruction {
        Instruction::ListLength { slot, keys, .. } => {
            vec![1, path_field_count(plan, *slot, keys)?, 4, 4]
        }
        Instruction::ListHead {
            slot,
            keys,
            schema,
            expressions,
        }
        | Instruction::ListPushFront {
            slot,
            keys,
            schema,
            expressions,
        } => {
            let parsed = checked_record_schema(schema)?;
            ensure!(
                expressions.len() == parsed.counts().leaves,
                "list record expression count mismatch"
            );
            let path = path_field_count(plan, *slot, keys)?;
            let n = expressions.len();
            if matches!(instruction, Instruction::ListHead { .. }) {
                vec![1, path, 4, 2 + 2 * n]
            } else {
                vec![path, 1, 4, 2, 6 + 2 * n, 1, 5, 1, 1, 1, 5, 1, 1]
            }
        }
        Instruction::ListPopFront { slot, keys } => {
            vec![path_field_count(plan, *slot, keys)?, 1, 4, 2, 1, 4, 1]
        }
        Instruction::ListReset { slot, keys } => {
            if let Some((_, parents)) = keys.split_last() {
                let full = path_field_count(plan, *slot, keys)?;
                let parent = path_field_count(plan, *slot, parents)?;
                vec![parent, 2 + full - parent, 8, 1]
            } else {
                vec![5, 8, 1]
            }
        }
        _ => vec![impact_field_count(instruction, plan)?],
    })
}

/// Number of transcript fields in one statically scheduled Impact group.
/// Inactive guarded writes use only this shape metadata, never their payloads.
fn impact_field_count(instruction: &Instruction, plan: &Plan) -> Result<usize> {
    let value_fields = |alignment: &str| -> Result<usize> {
        match alignment {
            "field" | "bit" | "u64" => Ok(1),
            "bytes32" => Ok(2),
            _ => bail!("unsupported alignment"),
        }
    };
    Ok(match instruction {
        Instruction::AddImmediate { .. } | Instruction::SubImmediate { .. } => 2,
        Instruction::Dup | Instruction::Member | Instruction::Insert { .. } | Instruction::New => 1,
        Instruction::Index { key: None, .. } => 4,
        Instruction::Index {
            slot, key: Some(_), ..
        } => {
            let key_type = map_key_type(plan, *slot)?;
            6 + value_fields(key_alignment(&key_type))?
        }
        Instruction::IndexPath { slot, keys, .. } => path_field_count(plan, *slot, keys)?,
        Instruction::ListLength { .. }
        | Instruction::ListHead { .. }
        | Instruction::ListPushFront { .. }
        | Instruction::ListPopFront { .. }
        | Instruction::ListReset { .. } => {
            impact_field_counts(instruction, plan)?.into_iter().sum()
        }
        Instruction::Push { alignment, .. } => 4 + value_fields(alignment)?,
        Instruction::Popeq { alignment, .. } => 3 + value_fields(alignment)?,
        Instruction::PushFields {
            expressions,
            schema,
            ..
        } => {
            let parsed = checked_record_schema(schema)?;
            ensure!(
                expressions.len() == parsed.counts().leaves,
                "record expression count mismatch"
            );
            3 + 2 * expressions.len()
        }
        Instruction::PopeqFields {
            expressions,
            schema,
        } => {
            let parsed = checked_record_schema(schema)?;
            ensure!(
                expressions.len() == parsed.counts().leaves,
                "record expression count mismatch"
            );
            2 + 2 * expressions.len()
        }
        Instruction::Guarded { .. } => bail!("nested guarded native operation is unsupported"),
    })
}

fn map_key_type(plan: &Plan, slot: u32) -> Result<ScalarType> {
    map_path_key_types(plan, slot, 1)?
        .pop()
        .ok_or_else(|| anyhow!("invalid map key schema"))
}

fn map_path_key_types(plan: &Plan, slot: u32, count: usize) -> Result<Vec<ScalarType>> {
    ensure!(count < 16, "map path exceeds native index limit");
    let state = plan
        .state
        .get(slot as usize)
        .ok_or_else(|| anyhow!("state slot out of range"))?;
    if count == 0 {
        return Ok(Vec::new());
    }
    if let Some(mut schema) = state.kind.get("tree") {
        let mut types = Vec::with_capacity(count);
        for _ in 0..count {
            let parts = schema
                .get("map")
                .and_then(Json::as_array)
                .filter(|parts| parts.len() == 2)
                .ok_or_else(|| anyhow!("map path exceeds declared schema"))?;
            let key = parts[0]
                .as_str()
                .ok_or_else(|| anyhow!("invalid map key schema"))?;
            types.push(ScalarType::parse(key)?);
            schema = &parts[1];
        }
        return Ok(types);
    }
    ensure!(count == 1, "scalar map has no nested path");
    let parts = state
        .kind
        .get("map")
        .and_then(Json::as_array)
        .filter(|parts| parts.len() == 2)
        .ok_or_else(|| anyhow!("invalid map key schema"))?;
    Ok(vec![ScalarType::parse(
        parts[0]
            .as_str()
            .ok_or_else(|| anyhow!("invalid map key schema"))?,
    )?])
}

fn validate_tree_schema(schema: &Json, depth: usize) -> Result<()> {
    ensure!(depth <= 16, "state tree exceeds native path limit");
    let fields = schema
        .as_object()
        .ok_or_else(|| anyhow!("invalid state tree schema"))?;
    ensure!(fields.len() == 1, "invalid state tree schema");
    if fields.get("counter") == Some(&Json::Bool(true)) {
        return Ok(());
    }
    if let Some(element) = fields.get("list") {
        let parts = element
            .as_object()
            .ok_or_else(|| anyhow!("invalid list element schema"))?;
        ensure!(parts.len() == 1, "invalid list element schema");
        checked_record_schema(
            parts
                .get("composite")
                .ok_or_else(|| anyhow!("list requires a Native record element"))?,
        )?;
        return Ok(());
    }
    if let Some(ty) = fields.get("scalar").and_then(Json::as_str) {
        ensure!(
            ScalarType::parse(ty)? != ScalarType::Bytes32,
            "bytes ledger values are unsupported"
        );
        return Ok(());
    }
    if let Some(schema) = fields.get("composite") {
        checked_record_schema(schema)?;
        return Ok(());
    }
    let parts = fields
        .get("map")
        .and_then(Json::as_array)
        .filter(|parts| parts.len() == 2)
        .ok_or_else(|| anyhow!("invalid state tree map schema"))?;
    ScalarType::parse(
        parts[0]
            .as_str()
            .ok_or_else(|| anyhow!("invalid state tree key type"))?,
    )?;
    validate_tree_schema(&parts[1], depth + 1)
}

fn checked_record_schema(json: &Json) -> Result<aggregates::Schema> {
    let schema = aggregates::Schema::from_json(&serde_json::to_vec(json)?)?;
    ensure!(
        schema.counts().leaves > 0 && schema.native_field_only(),
        "record requires nonempty Native leaves"
    );
    Ok(schema)
}

fn aligned_fields(fields: &[Fr]) -> AlignedValue {
    let fields: Vec<_> = fields.iter().copied().map(field_value).collect();
    AlignedValue::concat(fields.iter())
}

fn validate_record_fields(schema: &aggregates::Schema, fields: &[Fr]) -> Result<()> {
    let json: Vec<_> = fields
        .iter()
        .map(|field| Json::String(field_decimal(*field)))
        .collect();
    schema.from_leaf_json(&json)?;
    Ok(())
}

fn record_component_names<'a>(
    read: &'a Read,
    expressions: &[Expr],
    schema: &Json,
) -> Result<Vec<&'a str>> {
    let checked = checked_record_schema(schema)?;
    ensure!(
        read.ty == "Composite"
            && read.schema.as_ref() == Some(schema)
            && read.components.len() == checked.counts().leaves
            && expressions.len() == read.components.len(),
        "record read schema mismatch"
    );
    let mut names = BTreeSet::new();
    for (component, expression) in read.components.iter().zip(expressions) {
        ensure!(
            component.ty == "Native" && names.insert(component.name.as_str()),
            "invalid record read component"
        );
        ensure!(
            matches!(expression, Expr::Reference { name } if name == &component.name),
            "record read expression differs from source component"
        );
    }
    Ok(read
        .components
        .iter()
        .map(|component| component.name.as_str())
        .collect())
}

fn key_alignment(ty: &ScalarType) -> &'static str {
    if *ty == ScalarType::Bytes32 {
        "bytes32"
    } else {
        "field"
    }
}
fn inactive_read_value(ty: &str) -> Result<Value> {
    Ok(match ScalarType::parse(ty)? {
        ScalarType::Native => Value::Native(Fr::from(0u64)),
        ScalarType::Bool => Value::Bool(false),
        ScalarType::UInt(maximum) => Value::UInt {
            number: BigUint::from(0u8),
            maximum,
        },
        ScalarType::Bytes32 => Value::Bytes(vec![0; 32]),
        ScalarType::JubjubScalar | ScalarType::JubjubPoint => {
            bail!("Jubjub ledger reads require typed coordinate records")
        }
    })
}
#[derive(Clone, Deserialize)]
pub struct Config {
    pub inputs: BTreeMap<String, Json>,
    pub state: BTreeMap<String, Json>,
    #[serde(rename = "negativeCases", default)]
    pub negative_cases: Vec<NegativeCase>,
}
/// Private decoding errors retain locations, never parser messages or values.
pub fn parse_private_config(bytes: &[u8]) -> Result<Config> {
    serde_json::from_slice(bytes).map_err(|error| {
        anyhow!(
            "invalid private configuration (line {}, column {})",
            error.line(),
            error.column()
        )
    })
}
#[derive(Clone, Deserialize)]
pub struct NegativeCase {
    pub name: String,
    pub inputs: BTreeMap<String, Json>,
}
fn input_value(ty: &str, json: &Json) -> Result<Value> {
    match ScalarType::parse(ty)? {
        ScalarType::Native => Ok(Value::Native(canonical_field(
            json.as_str()
                .ok_or_else(|| anyhow!("Native input requires decimal string"))?,
        )?)),
        ScalarType::Bool => Ok(Value::Bool(
            json.as_bool()
                .ok_or_else(|| anyhow!("Bool input requires boolean"))?,
        )),
        ScalarType::UInt(maximum) => Ok(Value::UInt {
            number: canonical_unsigned(
                json.as_str()
                    .ok_or_else(|| anyhow!("unsigned input requires decimal string"))?,
                &maximum,
            )?,
            maximum,
        }),
        ScalarType::Bytes32 => {
            let object = json
                .as_object()
                .ok_or_else(|| anyhow!("expected bytes object"))?;
            ensure!(
                object.len() == 2 && object.get("kind").and_then(Json::as_str) == Some("bytes"),
                "invalid bytes object"
            );
            let values = object
                .get("values")
                .and_then(Json::as_array)
                .ok_or_else(|| anyhow!("expected bytes array"))?;
            ensure!(values.len() == 32, "expected 32 bytes");
            let bytes = values
                .iter()
                .map(|value| {
                    value
                        .as_u64()
                        .and_then(|value| u8::try_from(value).ok())
                        .ok_or_else(|| anyhow!("expected canonical byte integer"))
                })
                .collect::<Result<Vec<_>>>()?;
            Ok(Value::Bytes(bytes))
        }
        ScalarType::JubjubScalar => {
            let object = json
                .as_object()
                .ok_or_else(|| anyhow!("expected JubjubScalar object"))?;
            ensure!(
                object.len() == 2
                    && object.get("kind").and_then(Json::as_str) == Some("jubjubScalar"),
                "invalid JubjubScalar object"
            );
            let value = object
                .get("value")
                .and_then(Json::as_str)
                .ok_or_else(|| anyhow!("JubjubScalar requires canonical decimal value"))?;
            Ok(Value::JubjubScalar(jubjub::scalar(value)?))
        }
        ScalarType::JubjubPoint => {
            let object = json
                .as_object()
                .ok_or_else(|| anyhow!("expected JubjubPoint object"))?;
            ensure!(
                object.len() == 3
                    && object.get("kind").and_then(Json::as_str) == Some("jubjubPoint"),
                "invalid JubjubPoint object"
            );
            let x = canonical_field(
                object
                    .get("x")
                    .and_then(Json::as_str)
                    .ok_or_else(|| anyhow!("JubjubPoint requires canonical x coordinate"))?,
            )?;
            let y = canonical_field(
                object
                    .get("y")
                    .and_then(Json::as_str)
                    .ok_or_else(|| anyhow!("JubjubPoint requires canonical y coordinate"))?,
            )?;
            Ok(Value::JubjubPoint(jubjub::point(x, y)?))
        }
    }
}
pub fn environment(plan: &Plan, inputs: &BTreeMap<String, Json>) -> Result<Environment> {
    ensure!(plan.schema_version == 1, "unsupported plan schema");
    ensure!(
        profile::validate_plan(plan.target.as_deref(), plan.target_profile.as_ref()),
        "plan target differs from linked native profile"
    );
    ensure!(!plan.entrypoint.is_empty(), "missing entrypoint");
    let names: BTreeSet<_> = plan.circuit.inputs.iter().map(|i| &i.name).collect();
    ensure!(
        names.len() == plan.circuit.inputs.len(),
        "duplicate input name"
    );
    ensure!(
        inputs.len() == names.len() && inputs.keys().all(|n| names.contains(n)),
        "input schema mismatch (missing or unknown input)"
    );
    let mut env = BTreeMap::new();
    for i in &plan.circuit.inputs {
        ensure!(
            matches!(i.visibility.as_str(), "public" | "private"),
            "unsupported input visibility"
        );
        env.insert(
            i.name.clone(),
            input_value(&i.ty, &inputs[&i.name])
                .with_context(|| format!("invalid input '{}'", i.name))?,
        );
    }
    for o in &plan.circuit.outputs {
        ensure!(o.visibility == "public", "unsupported output visibility");
        ensure!(!env.contains_key(&o.name), "output shadows existing name");
        let v = evaluate(&o.expression, &env)?;
        ensure!(
            v.scalar_type() == ScalarType::parse(&o.ty)?,
            "output type mismatch"
        );
        env.insert(o.name.clone(), v);
    }
    Ok(env)
}
pub fn create_state(plan: &Plan, config: &BTreeMap<String, Json>) -> Result<ChargedState<Db>> {
    ensure!(plan.state.len() <= 16, "state array exceeds native limit");
    ensure!(
        config.len() == plan.state.len(),
        "initial state schema mismatch"
    );
    let mut values = Vec::new();
    for d in &plan.state {
        let value = config
            .get(&d.name)
            .ok_or_else(|| anyhow!("missing initial state cell"))?;
        if let Some(ty) = d.kind.get("cell").and_then(Json::as_str) {
            values.push(StateValue::Cell(Sp::new(aligned(
                &input_value(ty, value)?,
                "field",
            )?)));
        } else if let Some(types) = d.kind.get("map").and_then(Json::as_array) {
            ensure!(
                types.len() == 2
                    && types
                        .iter()
                        .all(|t| t.as_str().is_some_and(|t| ScalarType::parse(t).is_ok())),
                "unsupported map schema"
            );
            ensure!(
                value.as_array().is_some_and(|a| a.is_empty()),
                "initial map must be explicitly empty"
            );
            values.push(StateValue::Map(Default::default()));
        } else if let Some(schema) = d.kind.get("tree") {
            validate_tree_schema(schema, 0)?;
            if schema.get("list").is_some() {
                ensure!(
                    value.as_array().is_some_and(Vec::is_empty),
                    "initial list must be empty"
                );
                values.push(empty_native_list());
            } else if schema.get("counter") == Some(&Json::Bool(true)) {
                values.push(StateValue::Cell(Sp::new(aligned(
                    &input_value("UIntRange<18446744073709551616>", value)?,
                    "u64",
                )?)));
            } else if let Some(ty) = schema.get("scalar").and_then(Json::as_str) {
                values.push(StateValue::Cell(Sp::new(aligned(
                    &input_value(ty, value)?,
                    "field",
                )?)));
            } else if let Some(schema) = schema.get("composite") {
                let schema = checked_record_schema(schema)?;
                let leaves = schema.flatten_leaves_json(&serde_json::to_vec(value)?)?;
                let fields = leaves
                    .iter()
                    .map(|leaf| {
                        canonical_field(
                            leaf.as_str()
                                .ok_or_else(|| anyhow!("record requires Native leaves"))?,
                        )
                    })
                    .collect::<Result<Vec<_>>>()?;
                values.push(StateValue::Cell(Sp::new(aligned_fields(&fields))));
            } else {
                ensure!(
                    value.as_array().is_some_and(|items| items.is_empty()),
                    "initial map tree must be explicitly empty"
                );
                values.push(StateValue::Map(Default::default()));
            }
        } else {
            bail!("unsupported state kind");
        }
    }
    Ok(ChargedState::new(StateValue::Array(
        values.into_iter().collect(),
    )))
}
fn read_state_value(
    context: &QueryContext<Db>,
    slot: u32,
    keys: &[AlignedValue],
) -> Result<StateValue<Db>> {
    let StateValue::Array(array) = context.state.get_ref() else {
        bail!("expected array state")
    };
    let mut cell = Sp::new(
        array
            .get(slot as usize)
            .ok_or_else(|| anyhow!("state slot out of range"))?
            .clone(),
    );
    for key in keys {
        cell = match &*cell {
            StateValue::Map(map) => map
                .get(key)
                .ok_or_else(|| anyhow!("missing map path key"))?,
            _ => bail!("state path does not address a map"),
        };
    }
    Ok((*cell).clone())
}

fn read_state_aligned(
    context: &QueryContext<Db>,
    slot: u32,
    keys: &[AlignedValue],
) -> Result<AlignedValue> {
    let StateValue::Cell(ref value) = read_state_value(context, slot, keys)? else {
        bail!("expected state cell")
    };
    Ok((**value).clone())
}

fn read_state_cell(
    context: &QueryContext<Db>,
    slot: u32,
    keys: &[AlignedValue],
    ty: &str,
    alignment: &str,
) -> Result<Value> {
    decode_state_cell(&read_state_aligned(context, slot, keys)?, ty, alignment)
}

fn decode_state_cell(value: &AlignedValue, ty: &str, alignment: &str) -> Result<Value> {
    let mut fields = Vec::new();
    value.value_only_field_repr(&mut fields);
    ensure!(fields.len() == 1, "expected scalar state cell");
    let decoded = match ScalarType::parse(ty)? {
        ScalarType::Native => Ok(Value::Native(fields[0])),
        ScalarType::Bool => Ok(Value::Bool(
            bool::try_from(fields[0]).map_err(|_| anyhow!("noncanonical state bool"))?,
        )),
        ScalarType::UInt(_) => input_value(ty, &Json::String(field_decimal(fields[0]))),
        ScalarType::Bytes32 => bail!("bytes ledger values are unsupported"),
        ScalarType::JubjubScalar | ScalarType::JubjubPoint => {
            bail!("Jubjub ledger values require typed coordinate records")
        }
    }?;
    ensure!(
        *value == aligned(&decoded, alignment)?,
        "state cell alignment or encoding mismatch"
    );
    Ok(decoded)
}

fn tree_schema_at_path(plan: &Plan, slot: u32, depth: usize) -> Result<&Json> {
    let mut schema = plan
        .state
        .get(slot as usize)
        .and_then(|state| state.kind.get("tree"))
        .ok_or_else(|| anyhow!("record path requires tree state"))?;
    ensure!(depth < 16, "record path exceeds native index limit");
    for _ in 0..depth {
        schema = schema
            .get("map")
            .and_then(Json::as_array)
            .filter(|parts| parts.len() == 2)
            .and_then(|parts| parts.get(1))
            .ok_or_else(|| anyhow!("record path exceeds declared schema"))?;
    }
    Ok(schema)
}

fn list_schema_at_path(plan: &Plan, slot: u32, depth: usize) -> Result<&Json> {
    ensure!(depth <= 13, "list path exceeds native insertion depth");
    tree_schema_at_path(plan, slot, depth)?
        .get("list")
        .and_then(|value| value.get("composite"))
        .ok_or_else(|| anyhow!("path does not select a Native-record List"))
}

fn empty_native_list() -> StateValue<Db> {
    StateValue::Array(
        vec![
            StateValue::Null,
            StateValue::Null,
            StateValue::Cell(Sp::new(0u64.into())),
        ]
        .into(),
    )
}

fn native_list_value(
    context: &QueryContext<Db>,
    slot: u32,
    keys: &[AlignedValue],
    schema: &Json,
) -> Result<(u64, Option<AlignedValue>)> {
    let StateValue::Array(ref node) = read_state_value(context, slot, keys)? else {
        bail!("expected native List array")
    };
    ensure!(node.len() == 3, "invalid native List node width");
    let StateValue::Cell(length) = node.get(2).unwrap() else {
        bail!("invalid List length cell")
    };
    let Value::UInt { number, .. } =
        decode_state_cell(length, "UIntRange<18446744073709551616>", "u64")?
    else {
        unreachable!()
    };
    let length = u64::try_from(number).map_err(|_| anyhow!("invalid List length"))?;
    if length == 0 {
        ensure!(
            matches!(node.get(0), Some(StateValue::Null))
                && matches!(node.get(1), Some(StateValue::Null)),
            "invalid empty List sentinel"
        );
        return Ok((0, None));
    }
    ensure!(
        matches!(node.get(1), Some(StateValue::Array(_))),
        "invalid List tail"
    );
    let StateValue::Cell(head) = node.get(0).unwrap() else {
        bail!("invalid List head cell")
    };
    let checked = checked_record_schema(schema)?;
    let mut fields = Vec::new();
    head.value_only_field_repr(&mut fields);
    ensure!(
        **head == aligned_fields(&fields),
        "List head alignment mismatch"
    );
    validate_record_fields(&checked, &fields)?;
    Ok((length, Some((**head).clone())))
}

fn list_index(index: u8) -> Op<ResultModeVerify, Db> {
    Op::Idx {
        cached: false,
        push_path: false,
        path: vec![Key::Value(
            AlignedValue::from(index).try_into().expect("u8 index"),
        )]
        .try_into()
        .expect("one index"),
    }
}

fn push_native_state(value: StateValue<Db>, storage: bool) -> Result<Op<ResultModeVerify, Db>> {
    Ok(Op::Push {
        storage,
        value: value
            .try_into_checked()
            .map_err(|_| anyhow!("invalid native List storage value"))?,
    })
}

fn record_schema_at_path(plan: &Plan, slot: u32, depth: usize) -> Result<&Json> {
    tree_schema_at_path(plan, slot, depth)?
        .get("composite")
        .ok_or_else(|| anyhow!("path does not select a record"))
}
fn native_index(
    plan: &Plan,
    slot: u32,
    keys: &[PathPart],
    push_path: bool,
    env: &Environment,
) -> Result<(Op<ResultModeVerify, Db>, Vec<AlignedValue>)> {
    let types = map_path_key_types(plan, slot, keys.len())?;
    let mut path = vec![Key::Value(
        field_value(Fr::from(slot as u64))
            .try_into()
            .map_err(|_| anyhow!("invalid native index key"))?,
    )];
    let mut values = Vec::with_capacity(keys.len());
    for (part, ty) in keys.iter().zip(types) {
        ensure!(
            part.alignment == key_alignment(&ty),
            "map path key alignment mismatch"
        );
        let value = aligned(&evaluate(&part.expression, env)?, &part.alignment)?;
        path.push(Key::Value(
            value
                .clone()
                .try_into()
                .map_err(|_| anyhow!("invalid native map key"))?,
        ));
        values.push(value);
    }
    Ok((
        Op::Idx {
            cached: false,
            push_path,
            path: path.into_iter().collect(),
        },
        values,
    ))
}
fn advance_native_state_prefix(
    context: &mut QueryContext<Db>,
    program: &[Op<ResultModeVerify, Db>],
    materialized: &mut usize,
    boundary: usize,
    cost: &onchain_runtime::cost_model::CostModel,
) -> Result<()> {
    ensure!(
        *materialized <= boundary && boundary <= program.len(),
        "invalid native state prefix boundary"
    );
    if *materialized == boundary {
        return Ok(());
    }
    *context = context
        .query(&program[*materialized..boundary], None, cost)
        .map_err(|_| anyhow!("native state prefix rejected"))?
        .context;
    *materialized = boundary;
    Ok(())
}

/// Gather the native VM's actual Bool result for a Member opcode. The gather
/// query replays only the current ordered prefix against the state after prior
/// writes, then appends a read to expose Member's result.
fn native_member_result(
    context: &QueryContext<Db>,
    program: &[Op<ResultModeVerify, Db>],
    cost: &onchain_runtime::cost_model::CostModel,
) -> Result<bool> {
    ensure!(
        matches!(program.last(), Some(Op::Member)),
        "membership read lacks a native Member opcode"
    );
    let mut gather_program: Vec<Op<ResultModeGather, Db>> = program
        .iter()
        .cloned()
        .map(|operation| operation.translate::<ResultModeGather, _>(|_| ()))
        .collect();
    gather_program.push(Op::Popeq {
        cached: false,
        result: (),
    });
    let result = context
        .query(&gather_program, None, cost)
        .map_err(|_| anyhow!("native map membership query rejected"))?
        .events
        .into_iter()
        .rev()
        .find_map(|event| match event {
            GatherEvent::Read(value) => Some(value),
            GatherEvent::Log(_) => None,
        })
        .ok_or_else(|| anyhow!("native map membership query returned no Bool"))?;
    let absent = aligned(&Value::Bool(false), "bit")?;
    let present = aligned(&Value::Bool(true), "bit")?;
    if result == absent {
        Ok(false)
    } else if result == present {
        Ok(true)
    } else {
        bail!("native Member returned a noncanonical Bool")
    }
}

fn aligned_call_returns(values: &[(String, Value)]) -> Result<AlignedValue> {
    let fields = values
        .iter()
        .map(|(_, value)| value.field_encoding())
        .collect::<Result<Vec<_>>>()?;
    Ok(aligned_fields(&fields))
}

pub struct Execution {
    pub program: Program,
    /// Exact source schedule returned by the checked native Impact groups.
    pub activity_schedule: Vec<Option<usize>>,
    pub after: QueryContext<Db>,
    pub guaranteed: Option<Transcript<Db>>,
    pub fallible: Option<Transcript<Db>>,
    pub preimage: ProofPreimage,
    return_values: Vec<(String, Value)>,
}
impl Execution {
    /// Typed source-declared results. Call `check` before treating them as checked.
    pub fn returns(&self) -> &[(String, Value)] {
        &self.return_values
    }
    pub fn returns_json(&self) -> BTreeMap<String, Json> {
        self.return_values
            .iter()
            .map(|(name, value)| (name.clone(), value.public_json()))
            .collect()
    }
    pub(crate) fn call_output(&self) -> Result<AlignedValue> {
        aligned_call_returns(&self.return_values)
    }
}
pub fn prepare(
    plan: &Plan,
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
    params: &LedgerParameters,
    address: ContractAddress,
) -> Result<Execution> {
    let mut env = environment(plan, inputs)?;
    let context = QueryContext::new(state.clone(), address);
    let cost = &params.cost_model.runtime_cost_model;
    let mut prefix_context = context.clone();
    let mut materialized_prefix = 0usize;
    let mut mutation_boundary = 0usize;
    let mut program: Program = Vec::new();
    let mut read_index = 0usize;
    let mut previous_index: Option<(u32, Vec<AlignedValue>)> = None;
    let mut member_result_pending = false;
    let mut has_written = false;
    let mut activity_schedule = Vec::with_capacity(plan.operations.len());
    for i in &plan.operations {
        let operation_start = program.len();
        let mut instruction_guard = None;
        let instruction = match i {
            Instruction::Guarded { guard, operation } => {
                ensure!(
                    matches!(
                        operation.as_ref(),
                        Instruction::Dup
                            | Instruction::Index {
                                push_path: false,
                                ..
                            }
                            | Instruction::Push { storage: false, .. }
                            | Instruction::Popeq { .. }
                            | Instruction::Member
                            | Instruction::Index {
                                push_path: true,
                                ..
                            }
                            | Instruction::Push { .. }
                            | Instruction::Insert { .. }
                            | Instruction::IndexPath { .. }
                            | Instruction::New
                            | Instruction::PushFields { .. }
                            | Instruction::PopeqFields { .. }
                            | Instruction::AddImmediate { .. }
                            | Instruction::SubImmediate { .. }
                            | Instruction::ListLength { .. }
                            | Instruction::ListHead { .. }
                            | Instruction::ListPushFront { .. }
                            | Instruction::ListPopFront { .. }
                            | Instruction::ListReset { .. }
                    ),
                    "guarded native operation has an unsupported shape"
                );
                let active = evaluate(guard, &env)?.boolean()?;
                if !active {
                    activity_schedule.extend(
                        impact_field_counts(operation.as_ref(), plan)?
                            .into_iter()
                            .map(Some),
                    );
                    if let Instruction::Popeq {
                        expression,
                        alignment,
                    } = operation.as_ref()
                    {
                        let read = plan
                            .reads
                            .get(read_index)
                            .ok_or_else(|| anyhow!("missing read schema for inactive read"))?;
                        ensure!(
                            read.guard.as_ref() == Some(guard),
                            "inactive read guard differs from the source read schema"
                        );
                        let read_reference = match expression {
                            Expr::Reference { name } => Some(name),
                            Expr::Cast { ty, value } if ty == "Native" => match value.as_ref() {
                                Expr::Reference { name } => Some(name),
                                _ => None,
                            },
                            _ => None,
                        };
                        ensure!(
                            read_reference == Some(&read.name),
                            "inactive read result differs from the source read schema"
                        );
                        ensure!(
                            matches!(alignment.as_str(), "field" | "bit" | "u64"),
                            "unsupported inactive read alignment"
                        );
                        read_index += 1;
                        env.insert(read.name.clone(), inactive_read_value(&read.ty)?);
                    }
                    if let Instruction::PopeqFields {
                        expressions,
                        schema,
                    } = operation.as_ref()
                    {
                        let read = plan
                            .reads
                            .get(read_index)
                            .ok_or_else(|| anyhow!("missing inactive record read schema"))?;
                        ensure!(
                            read.guard.as_ref() == Some(guard),
                            "inactive record read guard mismatch"
                        );
                        for name in record_component_names(read, expressions, schema)? {
                            ensure!(
                                !env.contains_key(name),
                                "record component shadows an existing value"
                            );
                            env.insert(name.to_owned(), Value::Native(Fr::from(0u64)));
                        }
                        read_index += 1;
                    }
                    match operation.as_ref() {
                        Instruction::ListLength { expression, .. } => {
                            let read = plan
                                .reads
                                .get(read_index)
                                .ok_or_else(|| anyhow!("missing inactive List length read"))?;
                            ensure!(
                                read.guard.as_ref() == Some(guard)
                                    && read.ty == "UIntRange<18446744073709551616>",
                                "inactive List length read schema mismatch"
                            );
                            ensure!(
                                matches!(expression, Expr::Reference { name } if name == &read.name),
                                "List length must bind its declared read"
                            );
                            ensure!(
                                !env.contains_key(&read.name),
                                "List length shadows an existing value"
                            );
                            env.insert(read.name.clone(), inactive_read_value(&read.ty)?);
                            read_index += 1;
                        }
                        Instruction::ListHead {
                            schema,
                            expressions,
                            ..
                        } => {
                            let read = plan
                                .reads
                                .get(read_index)
                                .ok_or_else(|| anyhow!("missing inactive List head read"))?;
                            ensure!(
                                read.guard.as_ref() == Some(guard),
                                "inactive List head guard mismatch"
                            );
                            for name in record_component_names(read, expressions, schema)? {
                                ensure!(
                                    !env.contains_key(name),
                                    "List head component shadows an existing value"
                                );
                                env.insert(name.to_owned(), Value::Native(Fr::from(0u64)));
                            }
                            read_index += 1;
                        }
                        _ => {}
                    }
                    continue;
                }
                instruction_guard = Some(guard);
                operation.as_ref()
            }
            _ => i,
        };
        if has_written
            && matches!(
                instruction,
                Instruction::ListLength { .. }
                    | Instruction::ListHead { .. }
                    | Instruction::ListPushFront { .. }
                    | Instruction::ListPopFront { .. }
                    | Instruction::ListReset { .. }
            )
        {
            advance_native_state_prefix(
                &mut prefix_context,
                &program,
                &mut materialized_prefix,
                mutation_boundary,
                cost,
            )?;
        }
        let mut current_index = None;
        let op = match instruction {
            Instruction::Guarded { .. } => {
                bail!("nested guarded native operation is unsupported")
            }
            Instruction::Dup => Op::Dup { n: 0 },
            Instruction::Index {
                slot,
                push_path,
                key,
            } => {
                let map_key = key
                    .as_ref()
                    .map(|key| {
                        let key_type = map_key_type(plan, *slot)?;
                        aligned(&evaluate(key, &env)?, key_alignment(&key_type))
                    })
                    .transpose()?;
                let mut path = vec![Key::Value(
                    field_value(Fr::from(*slot as u64))
                        .try_into()
                        .map_err(|_| anyhow!("invalid native index key"))?,
                )];
                if let Some(key) = map_key.as_ref() {
                    path.push(Key::Value(
                        key.clone()
                            .try_into()
                            .map_err(|_| anyhow!("invalid native map key"))?,
                    ));
                }
                current_index = Some((*slot, map_key.into_iter().collect::<Vec<_>>()));
                Op::Idx {
                    cached: false,
                    push_path: *push_path,
                    path: path.into_iter().collect(),
                }
            }
            Instruction::IndexPath {
                slot,
                push_path,
                keys,
            } => {
                let (op, values) = native_index(plan, *slot, keys, *push_path, &env)?;
                current_index = Some((*slot, values));
                op
            }
            Instruction::New => Op::New,
            Instruction::Push {
                storage,
                expression,
                alignment,
            } => Op::Push {
                storage: *storage,
                value: StateValue::Cell(Sp::new(aligned(&evaluate(expression, &env)?, alignment)?))
                    .try_into_checked()
                    .map_err(|_| anyhow!("invalid native pushed value"))?,
            },
            Instruction::PushFields {
                storage,
                expressions,
                schema,
            } => {
                let schema = checked_record_schema(schema)?;
                let fields = expressions
                    .iter()
                    .map(|expression| evaluate(expression, &env)?.field())
                    .collect::<Result<Vec<_>>>()?;
                validate_record_fields(&schema, &fields)?;
                Op::Push {
                    storage: *storage,
                    value: StateValue::Cell(Sp::new(aligned_fields(&fields)))
                        .try_into_checked()
                        .map_err(|_| anyhow!("invalid native record value"))?,
                }
            }
            Instruction::Popeq {
                expression,
                alignment,
            } => {
                let read = plan
                    .reads
                    .get(read_index)
                    .ok_or_else(|| anyhow!("missing read schema"))?;
                ensure!(
                    read.guard.as_ref() == instruction_guard,
                    "active read guard differs from the source read schema"
                );
                read_index += 1;
                let read_reference = match expression {
                    Expr::Reference { name } => Some(name),
                    Expr::Cast { ty, value } if ty == "Native" => match value.as_ref() {
                        Expr::Reference { name } => Some(name),
                        _ => None,
                    },
                    _ => None,
                };
                if let Some(name) = read_reference {
                    if !env.contains_key(name) {
                        let member_read = member_result_pending
                            && read.ty == "Bool"
                            && alignment == "bit"
                            && name == &read.name;
                        if has_written {
                            advance_native_state_prefix(
                                &mut prefix_context,
                                &program,
                                &mut materialized_prefix,
                                mutation_boundary,
                                cost,
                            )?;
                        }
                        let read_context = if has_written {
                            &prefix_context
                        } else {
                            &context
                        };
                        let value = if member_read {
                            Value::Bool(native_member_result(
                                read_context,
                                &program[materialized_prefix..],
                                cost,
                            )?)
                        } else {
                            let (slot, keys) = previous_index
                                .as_ref()
                                .ok_or_else(|| anyhow!("unsupported state-read shape"))?;
                            if alignment == "u64" {
                                ensure!(
                                    tree_schema_at_path(plan, *slot, keys.len())?.get("counter")
                                        == Some(&Json::Bool(true)),
                                    "counter read path schema mismatch"
                                );
                            }
                            read_state_cell(read_context, *slot, keys, &read.ty, alignment)?
                        };
                        env.insert(name.clone(), value);
                    }
                }
                let value = evaluate(expression, &env)?;
                if !env.contains_key(&read.name) {
                    env.insert(read.name.clone(), value.clone());
                }
                Op::Popeq {
                    cached: false,
                    result: aligned(&value, alignment)?,
                }
            }
            Instruction::PopeqFields {
                expressions,
                schema,
            } => {
                let read = plan
                    .reads
                    .get(read_index)
                    .ok_or_else(|| anyhow!("missing record read schema"))?;
                ensure!(
                    read.guard.as_ref() == instruction_guard,
                    "active record read guard mismatch"
                );
                let names = record_component_names(read, expressions, schema)?;
                let (slot, keys) = previous_index
                    .as_ref()
                    .ok_or_else(|| anyhow!("record read lacks a native index"))?;
                ensure!(
                    record_schema_at_path(plan, *slot, keys.len())? == schema,
                    "record read differs from state schema"
                );
                if has_written {
                    advance_native_state_prefix(
                        &mut prefix_context,
                        &program,
                        &mut materialized_prefix,
                        mutation_boundary,
                        cost,
                    )?;
                }
                let read_context = if has_written {
                    &prefix_context
                } else {
                    &context
                };
                let value = read_state_aligned(read_context, *slot, keys)?;
                let expected_alignment =
                    aligned_fields(&vec![Fr::from(0u64); names.len()]).alignment;
                ensure!(
                    value.alignment == expected_alignment,
                    "record cell alignment mismatch"
                );
                let mut fields = Vec::new();
                value.value_only_field_repr(&mut fields);
                validate_record_fields(&checked_record_schema(schema)?, &fields)?;
                for (name, field) in names.into_iter().zip(fields) {
                    ensure!(
                        !env.contains_key(name),
                        "record component shadows an existing value"
                    );
                    env.insert(name.to_owned(), Value::Native(field));
                }
                read_index += 1;
                Op::Popeq {
                    cached: false,
                    result: value,
                }
            }
            Instruction::ListLength {
                slot,
                keys,
                expression,
            } => {
                let schema = list_schema_at_path(plan, *slot, keys.len())?;
                let (index, values) = native_index(plan, *slot, keys, false, &env)?;
                let read = plan
                    .reads
                    .get(read_index)
                    .ok_or_else(|| anyhow!("missing List length read"))?;
                ensure!(
                    read.guard.as_ref() == instruction_guard
                        && read.ty == "UIntRange<18446744073709551616>",
                    "List length read schema mismatch"
                );
                ensure!(
                    matches!(expression, Expr::Reference { name } if name == &read.name),
                    "List length must bind its declared read"
                );
                let (length, _) = native_list_value(
                    if has_written {
                        &prefix_context
                    } else {
                        &context
                    },
                    *slot,
                    &values,
                    schema,
                )?;
                ensure!(
                    !env.contains_key(&read.name),
                    "List length shadows an existing value"
                );
                env.insert(
                    read.name.clone(),
                    Value::UInt {
                        number: length.into(),
                        maximum: u64::MAX.into(),
                    },
                );
                read_index += 1;
                program.extend([Op::Dup { n: 0 }, index, list_index(2)]);
                Op::Popeq {
                    cached: false,
                    result: length.into(),
                }
            }
            Instruction::ListHead {
                slot,
                keys,
                schema,
                expressions,
            } => {
                ensure!(
                    list_schema_at_path(plan, *slot, keys.len())? == schema,
                    "List head schema mismatch"
                );
                let (index, values) = native_index(plan, *slot, keys, false, &env)?;
                let read = plan
                    .reads
                    .get(read_index)
                    .ok_or_else(|| anyhow!("missing List head read"))?;
                ensure!(
                    read.guard.as_ref() == instruction_guard,
                    "List head guard mismatch"
                );
                let names = record_component_names(read, expressions, schema)?;
                let (_, head) = native_list_value(
                    if has_written {
                        &prefix_context
                    } else {
                        &context
                    },
                    *slot,
                    &values,
                    schema,
                )?;
                let head = head.ok_or_else(|| anyhow!("head of empty List"))?;
                let mut fields = Vec::new();
                head.value_only_field_repr(&mut fields);
                for (name, value) in names.into_iter().zip(fields) {
                    ensure!(
                        !env.contains_key(name),
                        "List head component shadows an existing value"
                    );
                    env.insert(name.to_owned(), Value::Native(value));
                }
                read_index += 1;
                program.extend([Op::Dup { n: 0 }, index, list_index(0)]);
                Op::Popeq {
                    cached: false,
                    result: head,
                }
            }
            Instruction::ListPushFront {
                slot,
                keys,
                schema,
                expressions,
            } => {
                ensure!(
                    list_schema_at_path(plan, *slot, keys.len())? == schema,
                    "List push schema mismatch"
                );
                let (index, values) = native_index(plan, *slot, keys, true, &env)?;
                native_list_value(
                    if has_written {
                        &prefix_context
                    } else {
                        &context
                    },
                    *slot,
                    &values,
                    schema,
                )?;
                let fields = expressions
                    .iter()
                    .map(|value| evaluate(value, &env)?.field())
                    .collect::<Result<Vec<_>>>()?;
                validate_record_fields(&checked_record_schema(schema)?, &fields)?;
                let node = StateValue::Array(
                    vec![
                        StateValue::Cell(Sp::new(aligned_fields(&fields))),
                        StateValue::Null,
                        StateValue::Null,
                    ]
                    .into(),
                );
                program.extend([
                    index,
                    Op::Dup { n: 0 },
                    list_index(2),
                    Op::Addi { immediate: 1 },
                    push_native_state(node, true)?,
                    Op::Swap { n: 0 },
                    push_native_state(StateValue::Cell(Sp::new(2u8.into())), false)?,
                    Op::Swap { n: 0 },
                    Op::Ins {
                        cached: false,
                        n: 1,
                    },
                    Op::Swap { n: 0 },
                    push_native_state(StateValue::Cell(Sp::new(1u8.into())), false)?,
                    Op::Swap { n: 0 },
                ]);
                has_written = true;
                Op::Ins {
                    cached: false,
                    n: (keys.len() + 2).try_into()?,
                }
            }
            Instruction::ListPopFront { slot, keys } => {
                let schema = list_schema_at_path(plan, *slot, keys.len())?;
                let (index, values) = native_index(plan, *slot, keys, true, &env)?;
                let (length, _) = native_list_value(
                    if has_written {
                        &prefix_context
                    } else {
                        &context
                    },
                    *slot,
                    &values,
                    schema,
                )?;
                ensure!(length > 0, "pop of empty List");
                // Subi enforces nonempty in the ledger VM as well as host preparation.
                program.extend([
                    index,
                    Op::Dup { n: 0 },
                    list_index(2),
                    Op::Subi { immediate: 1 },
                    Op::Pop,
                    list_index(1),
                ]);
                has_written = true;
                Op::Ins {
                    cached: false,
                    n: (keys.len() + 1).try_into()?,
                }
            }
            Instruction::ListReset { slot, keys } => {
                list_schema_at_path(plan, *slot, keys.len())?;
                let (_, values) = native_index(plan, *slot, keys, false, &env)?;
                if let Some((_, parents)) = keys.split_last() {
                    let (index, _) = native_index(plan, *slot, parents, true, &env)?;
                    program.push(index);
                    program.push(push_native_state(
                        StateValue::Cell(Sp::new(values.last().expect("nonempty path").clone())),
                        false,
                    )?);
                } else {
                    program.push(push_native_state(
                        StateValue::Cell(Sp::new(field_value(Fr::from(*slot as u64)))),
                        false,
                    )?);
                }
                program.push(push_native_state(empty_native_list(), true)?);
                has_written = true;
                Op::Ins {
                    cached: false,
                    n: (keys.len() + 1).try_into()?,
                }
            }
            Instruction::Member => Op::Member,
            Instruction::AddImmediate { amount } | Instruction::SubImmediate { amount } => {
                let (slot, keys) = previous_index
                    .as_ref()
                    .ok_or_else(|| anyhow!("counter adjustment requires a complete index path"))?;
                ensure!(
                    tree_schema_at_path(plan, *slot, keys.len())?.get("counter")
                        == Some(&Json::Bool(true)),
                    "counter adjustment path schema mismatch"
                );
                if has_written {
                    advance_native_state_prefix(
                        &mut prefix_context,
                        &program,
                        &mut materialized_prefix,
                        mutation_boundary,
                        cost,
                    )?;
                }
                let read_context = if has_written {
                    &prefix_context
                } else {
                    &context
                };
                read_state_cell(
                    read_context,
                    *slot,
                    keys,
                    "UIntRange<18446744073709551616>",
                    "u64",
                )?;
                if matches!(instruction, Instruction::AddImmediate { .. }) {
                    Op::Addi { immediate: *amount }
                } else {
                    Op::Subi { immediate: *amount }
                }
            }
            Instruction::Insert { n } => {
                has_written = true;
                ensure!(*n > 0 && *n < 16, "unsupported insertion depth");
                Op::Ins {
                    cached: false,
                    n: *n,
                }
            }
        };
        previous_index = current_index;
        program.push(op);
        activity_schedule.extend(std::iter::repeat_n(None, program.len() - operation_start));
        member_result_pending = matches!(instruction, Instruction::Member);
        if matches!(
            instruction,
            Instruction::Insert { .. }
                | Instruction::ListPushFront { .. }
                | Instruction::ListPopFront { .. }
                | Instruction::ListReset { .. }
        ) {
            mutation_boundary = program.len();
        }
    }
    ensure!(
        activity_schedule
            .iter()
            .filter(|entry| entry.is_none())
            .count()
            == program.len(),
        "native activity schedule does not match emitted operations"
    );
    ensure!(read_index == plan.reads.len(), "read schema mismatch");
    context.query(&program, None, cost).map_err(|_| {
        anyhow!("native state transcript rejected (spent nullifier or state mismatch)")
    })?;
    ensure!(plan.returns.len() <= 256, "too many call returns");
    let mut return_values = Vec::with_capacity(plan.returns.len());
    let mut return_names = BTreeSet::new();
    for output in &plan.returns {
        ensure!(
            output.visibility == "public"
                && !output.name.is_empty()
                && return_names.insert(output.name.as_str()),
            "invalid call return declaration"
        );
        let ty = ScalarType::parse(&output.ty)?;
        ensure!(
            matches!(
                ty,
                ScalarType::Native | ScalarType::Bool | ScalarType::UInt(_)
            ),
            "call returns currently require Native, Bool or UInt"
        );
        let value = evaluate(&output.expression, &env)?;
        ensure!(value.scalar_type() == ty, "call return type mismatch");
        value.validate()?;
        return_values.push((output.name.clone(), value));
    }
    let output = aligned_call_returns(&return_values)?;
    let randomness = Fr::from(0u64); // Diagnostic checker context. Final transactions need fresh randomness.
    let empty = AlignedValue {
        value: FabValue(vec![]),
        alignment: Alignment(vec![]),
    };
    let comm = onchain_runtime::communication_commitment(empty, output, randomness);
    let partition = partition_transcripts(
        &[PreTranscript {
            context: context.clone(),
            program: program.clone(),
            comm_comm: Some(comm),
        }],
        params,
    )
    .map_err(|_| anyhow!("native transcript partitioning failed"))?;
    let (guaranteed, fallible) = partition
        .into_iter()
        .next()
        .ok_or_else(|| anyhow!("missing transcript partition"))?;
    let mut after = context;
    if let Some(t) = &guaranteed {
        after = after
            .run_transcript(t, cost)
            .map_err(|_| anyhow!("guaranteed transcript failed"))?
            .context;
    }
    if let Some(t) = &fallible {
        after = after
            .run_transcript(t, cost)
            .map_err(|_| anyhow!("fallible transcript failed"))?
            .context;
    }
    let mut public_transcript_inputs = Vec::new();
    let mut public_transcript_outputs = Vec::new();
    for op in guaranteed
        .iter()
        .chain(fallible.iter())
        .flat_map(|t| t.program.iter_deref())
    {
        op.field_repr(&mut public_transcript_inputs);
        if let Op::Popeq { result, .. } = op {
            result.value_only_field_repr(&mut public_transcript_outputs);
        }
    }
    let mut private_transcript = Vec::new();
    for input in plan
        .circuit
        .inputs
        .iter()
        .filter(|i| i.visibility == "private")
    {
        match &env[&input.name] {
            Value::Bytes(bytes) => {
                private_transcript.extend(bytes.iter().map(|byte| Fr::from(*byte as u64)))
            }
            Value::JubjubScalar(value) => private_transcript.push(jubjub::scalar_native(*value)?),
            Value::JubjubPoint(value) => private_transcript.extend(jubjub::coordinates(*value)?),
            value => aligned(value, "field")?.value_only_field_repr(&mut private_transcript),
        }
    }
    let preimage = ProofPreimage {
        inputs: vec![],
        private_transcript,
        public_transcript_inputs,
        public_transcript_outputs,
        binding_input: Fr::from(0u64),
        communications_commitment: Some((comm, randomness)),
        key_location: KeyLocation(Cow::Owned(plan.entrypoint.clone())),
    };
    Ok(Execution {
        program,
        activity_schedule,
        after,
        guaranteed,
        fallible,
        preimage,
        return_values,
    })
}
pub fn check(execution: &Execution, circuit: &IrSource) -> Result<Vec<Option<usize>>> {
    let (commitment, randomness) = execution
        .preimage
        .communications_commitment
        .ok_or_else(|| anyhow!("missing call output commitment"))?;
    let empty = AlignedValue {
        value: FabValue(vec![]),
        alignment: Alignment(vec![]),
    };
    ensure!(
        onchain_runtime::communication_commitment(empty, execution.call_output()?, randomness)
            == commitment,
        "call returns differ from the committed output"
    );
    let active = execution
        .preimage
        .check(circuit)
        .map_err(|_| anyhow!("native circuit assertion or preimage check failed"))?;
    ensure!(
        active == execution.activity_schedule,
        "activity metadata does not match source operation guards"
    );
    ensure!(
        active.iter().filter(|skip| skip.is_none()).count() == execution.program.len(),
        "active activity groups do not match native operations"
    );
    Ok(active)
}

/// Versioned C ABI over the bounded provider/session runtime.
pub mod ffi;

mod jubjub;
mod scalars;
pub use scalars::{MAX_UINT_BITS, ScalarType, canonical_unsigned, max_uint};

/// Versioned portable artifact manifests.
pub mod artifacts;
pub use artifacts::ContractBundleSet;

/// Native private transaction artifact assembly.
pub mod assembly;

/// Scoped host providers and private journal transport.
pub mod host;
/// Pure private-state lifecycle model.
pub mod lifecycle;
pub mod witness;
/// Owned source witness execution, native proof and client handoff.
pub mod witness_execution;

#[cfg(all(feature = "zkir-320", feature = "zkir-321"))]
compile_error!("select exactly one native profile: zkir-320 or zkir-321");
#[cfg(not(any(feature = "zkir-320", feature = "zkir-321")))]
compile_error!("select exactly one native profile: zkir-320 or zkir-321");
#[cfg(feature = "zkir-320")]
pub use zkir_320 as zkir;
#[cfg(all(feature = "zkir-321", not(feature = "zkir-320")))]
pub use zkir_321 as zkir;
pub mod aggregates;
pub mod native_ffi;
pub mod profile;
pub mod proof;
// Reply constructors live in explicitly selected native host adapters.
pub mod client;
pub mod control;
pub mod control_ffi;
#[cfg(all(feature = "localnet", feature = "zkir-321"))]
pub mod deployment_audit;
pub mod funding;
#[cfg(feature = "localnet")]
pub mod localnet;
#[cfg(feature = "localnet")]
pub mod localnet_ffi;
#[cfg_attr(not(feature = "localnet"), allow(dead_code))]
mod native_client;
