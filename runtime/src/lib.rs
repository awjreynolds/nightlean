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
        _ => bail!("unsupported alignment"),
    }
}
#[derive(Clone, Debug, Deserialize)]
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
}
#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "op", rename_all = "lowercase", deny_unknown_fields)]
pub enum Instruction {
    Dup,
    Index {
        slot: u32,
        #[serde(rename = "pushPath")]
        push_path: bool,
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
    }
}
pub struct Execution {
    pub program: Program,
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
    let mut program: Program = Vec::new();
    let mut read_index = 0usize;
    let mut previous_slot = None;
    let mut has_written = false;
    for i in &plan.operations {
        let op = match i {
            Instruction::Dup => Op::Dup { n: 0 },
            Instruction::Index { slot, push_path } => Op::Idx {
                cached: false,
                push_path: *push_path,
                path: vec![Key::Value(
                    field_value(Fr::from(*slot as u64))
                        .try_into()
                        .map_err(|_| anyhow!("invalid native index key"))?,
                )]
                .into_iter()
                .collect(),
            },
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
                        ensure!(
                            !has_written,
                            "state reads after writes are not qualified in this runtime slice"
                        );
                        env.insert(
                            name.clone(),
                            read_cell(
                                &context,
                                previous_slot
                                    .ok_or_else(|| anyhow!("unsupported state-read shape"))?,
                                &read.ty,
                            )?,
                        );
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
        previous_slot = match i {
            Instruction::Index { slot, .. } => Some(*slot),
            _ => None,
        };
        program.push(op);
    }
    ensure!(read_index == plan.reads.len(), "read schema mismatch");
    let cost = &params.cost_model.runtime_cost_model;
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
        aligned(&env[&input.name], "field")?.value_only_field_repr(&mut private_transcript);
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
        active.len() == execution.program.len(),
        "activity metadata does not match native operations"
    );
    Ok(active)
}

/// Versioned C ABI over the bounded provider/session runtime.
pub mod ffi;

mod scalars;
pub use scalars::{MAX_UINT_BITS, ScalarType, canonical_unsigned, max_uint};

/// Versioned portable artifact manifests.
pub mod artifacts;

/// Native private transaction artifact assembly.
pub mod assembly;

/// Scoped host providers and private journal transport.
pub mod host;
/// Pure private-state lifecycle model.
pub mod lifecycle;

#[cfg(all(feature = "zkir-320", feature = "zkir-321"))]
compile_error!("select exactly one native profile: zkir-320 or zkir-321");
#[cfg(not(any(feature = "zkir-320", feature = "zkir-321")))]
compile_error!("select exactly one native profile: zkir-320 or zkir-321");
#[cfg(feature = "zkir-320")]
pub use zkir_320 as zkir;
#[cfg(all(feature = "zkir-321", not(feature = "zkir-320")))]
pub use zkir_321 as zkir;
pub mod profile;
pub mod aggregates;
