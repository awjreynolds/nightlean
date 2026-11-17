//! Native execution of the bounded Nightlean plan schema. No process or JavaScript API.
use crate::zkir::IrSource;
use anyhow::{Context, Result, anyhow, bail, ensure};
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
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
use std::{
    borrow::Cow,
    collections::{BTreeMap, BTreeSet},
};
use storage::{arena::Sp, db::InMemoryDB};
use transient_crypto::{
    curve::Fr,
    fab::AlignedValueExt,
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
    Push {
        storage: bool,
        expression: Expr,
        alignment: String,
    },
    Popeq {
        expression: Expr,
        alignment: String,
    },
    Member,
    Insert {
        n: u8,
    },
}

/// Number of transcript fields in one statically scheduled Impact group.
/// Inactive guarded writes use only this shape metadata, never their payloads.
fn impact_field_count(instruction: &Instruction, plan: &Plan) -> Result<usize> {
    let value_fields = |alignment: &str| -> Result<usize> {
        match alignment {
            "field" | "bit" => Ok(1),
            "bytes32" => Ok(2),
            _ => bail!("unsupported alignment"),
        }
    };
    Ok(match instruction {
        Instruction::Dup | Instruction::Member | Instruction::Insert { .. } => 1,
        Instruction::Index { key: None, .. } => 4,
        Instruction::Index {
            slot, key: Some(_), ..
        } => {
            let key_type = map_key_type(plan, *slot)?;
            6 + value_fields(key_alignment(&key_type))?
        }
        Instruction::Push { alignment, .. } => 4 + value_fields(alignment)?,
        Instruction::Popeq { alignment, .. } => 3 + value_fields(alignment)?,
        Instruction::Guarded { .. } => bail!("nested guarded native operation is unsupported"),
    })
}

fn map_key_type(plan: &Plan, slot: u32) -> Result<ScalarType> {
    let ty = plan
        .state
        .get(slot as usize)
        .and_then(|state| state.kind.get("map"))
        .and_then(Json::as_array)
        .and_then(|types| types.first())
        .and_then(Json::as_str)
        .ok_or_else(|| anyhow!("invalid map key schema"))?;
    ScalarType::parse(ty)
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
        } else {
            bail!("unsupported state kind");
        }
    }
    Ok(ChargedState::new(StateValue::Array(
        values.into_iter().collect(),
    )))
}
fn read_cell(context: &QueryContext<Db>, slot: u32, ty: &str) -> Result<Value> {
    let StateValue::Array(array) = context.state.get_ref() else {
        bail!("expected array state")
    };
    let cell = array
        .get(slot as usize)
        .ok_or_else(|| anyhow!("state slot out of range"))?;
    let StateValue::Cell(value) = &*cell else {
        bail!("expected state cell")
    };
    let mut fields = Vec::new();
    value.value_only_field_repr(&mut fields);
    ensure!(fields.len() == 1, "expected scalar state cell");
    match ScalarType::parse(ty)? {
        ScalarType::Native => Ok(Value::Native(fields[0])),
        ScalarType::Bool => Ok(Value::Bool(
            bool::try_from(fields[0]).map_err(|_| anyhow!("noncanonical state bool"))?,
        )),
        ScalarType::UInt(_) => input_value(ty, &Json::String(field_decimal(fields[0]))),
        ScalarType::Bytes32 => bail!("bytes ledger values are unsupported"),
    }
}
fn read_map_cell(
    context: &QueryContext<Db>,
    slot: u32,
    key: &AlignedValue,
    ty: &str,
) -> Result<Value> {
    let StateValue::Array(array) = context.state.get_ref() else {
        bail!("expected array state")
    };
    let map = array
        .get(slot as usize)
        .ok_or_else(|| anyhow!("state slot out of range"))?;
    let StateValue::Map(map) = &*map else {
        bail!("expected state map")
    };
    let value = map.get(key).ok_or_else(|| anyhow!("missing map key"))?;
    let StateValue::Cell(value) = &*value else {
        bail!("expected map value cell")
    };
    let mut fields = Vec::new();
    value.value_only_field_repr(&mut fields);
    ensure!(fields.len() == 1, "expected scalar map value");
    match ScalarType::parse(ty)? {
        ScalarType::Native => Ok(Value::Native(fields[0])),
        ScalarType::Bool => Ok(Value::Bool(
            bool::try_from(fields[0]).map_err(|_| anyhow!("noncanonical state bool"))?,
        )),
        ScalarType::UInt(_) => input_value(ty, &Json::String(field_decimal(fields[0]))),
        ScalarType::Bytes32 => bail!("bytes ledger values are unsupported"),
    }
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

pub struct Execution {
    pub program: Program,
    /// Exact source schedule returned by the checked native Impact groups.
    pub activity_schedule: Vec<Option<usize>>,
    pub after: QueryContext<Db>,
    pub guaranteed: Option<Transcript<Db>>,
    pub fallible: Option<Transcript<Db>>,
    pub preimage: ProofPreimage,
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
    let mut previous_index = None;
    let mut member_result_pending = false;
    let mut has_written = false;
    let mut activity_schedule = Vec::with_capacity(plan.operations.len());
    for i in &plan.operations {
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
                    ),
                    "guarded native operation has an unsupported shape"
                );
                let active = evaluate(guard, &env)?.boolean()?;
                activity_schedule.push(if active {
                    None
                } else {
                    Some(impact_field_count(operation.as_ref(), plan)?)
                });
                if !active {
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
                            matches!(alignment.as_str(), "field" | "bit"),
                            "unsupported inactive read alignment"
                        );
                        read_index += 1;
                        env.insert(read.name.clone(), inactive_read_value(&read.ty)?);
                    }
                    continue;
                }
                instruction_guard = Some(guard);
                operation.as_ref()
            }
            _ => {
                activity_schedule.push(None);
                i
            }
        };
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
                current_index = Some((*slot, map_key));
                Op::Idx {
                    cached: false,
                    push_path: *push_path,
                    path: path.into_iter().collect(),
                }
            }
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
                            let (slot, key) = previous_index
                                .as_ref()
                                .ok_or_else(|| anyhow!("unsupported state-read shape"))?;
                            match key {
                                Some(key) => read_map_cell(read_context, *slot, key, &read.ty)?,
                                None => read_cell(read_context, *slot, &read.ty)?,
                            }
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
            Instruction::Member => Op::Member,
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
        member_result_pending = matches!(instruction, Instruction::Member);
        if matches!(instruction, Instruction::Insert { .. }) {
            mutation_boundary = program.len();
        }
    }
    ensure!(
        activity_schedule.len() == plan.operations.len(),
        "native activity schedule does not match source operations"
    );
    ensure!(read_index == plan.reads.len(), "read schema mismatch");
    context.query(&program, None, cost).map_err(|_| {
        anyhow!("native state transcript rejected (spent nullifier or state mismatch)")
    })?;
    let randomness = Fr::from(0u64); // Diagnostic checker context. Final transactions need fresh randomness.
    let empty = AlignedValue {
        value: FabValue(vec![]),
        alignment: Alignment(vec![]),
    };
    let comm = onchain_runtime::communication_commitment(empty.clone(), empty, randomness);
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
    })
}
pub fn check(execution: &Execution, circuit: &IrSource) -> Result<Vec<Option<usize>>> {
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
