//! Host-only structured execution. This plan never authenticates native proof or ledger guards.
use crate::{ScalarType, Value, canonical_field, host, input_value, max_uint, scalars};
use anyhow::{Result, anyhow, bail, ensure};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::{
    collections::{BTreeMap, BTreeSet},
    sync::Arc,
};
use zeroize::Zeroize;

pub const MAX_BYTES: usize = 1_048_576;
pub const MAX_STEPS: usize = 131_072;
const MAX_NODES: usize = 16_384;
const MAX_DEPTH: usize = 128;
const MAX_FUNCTIONS: usize = 256;
const MAX_ARGUMENTS: usize = 64;
const MAX_WITNESSES: usize = 32;

#[derive(Clone, Debug, PartialEq, Eq)]
enum Type {
    Unit,
    Scalar(ScalarType),
}
impl Type {
    fn parse(text: &str) -> Result<Self> {
        if text == "Unit" {
            Ok(Self::Unit)
        } else {
            Ok(Self::Scalar(ScalarType::parse(text)?))
        }
    }
    fn coerce(&self, mut value: Tracked) -> Result<Tracked> {
        value.known = known_cast(self, value.known.take());
        value.value = match (self, value.value) {
            (Self::Unit, None) => None,
            (Self::Scalar(ty), Some(value)) => Some(value.cast(ty)?),
            _ => bail!("control value type mismatch"),
        };
        Ok(value)
    }
}
fn subtype(a: &Type, b: &Type) -> bool {
    a == b
        || matches!(
            (a, b),
            (
                Type::Scalar(ScalarType::UInt(_)),
                Type::Scalar(ScalarType::Native)
            )
        )
        || matches!((a,b), (Type::Scalar(ScalarType::UInt(m)),Type::Scalar(ScalarType::UInt(n))) if m<=n)
}
fn join(a: &Type, b: &Type) -> Result<Type> {
    if subtype(a, b) {
        Ok(b.clone())
    } else if subtype(b, a) {
        Ok(a.clone())
    } else {
        bail!("control branch type mismatch")
    }
}
fn scalar_type(ty: &Type) -> Result<&ScalarType> {
    match ty {
        Type::Scalar(t) => Ok(t),
        _ => bail!("control scalar required"),
    }
}
fn text<'a>(v: &'a Json, key: &str) -> Result<&'a str> {
    v.get(key)
        .and_then(Json::as_str)
        .ok_or_else(|| anyhow!("invalid control descriptor"))
}
fn field<'a>(v: &'a Json, key: &str) -> Result<&'a Json> {
    v.get(key)
        .ok_or_else(|| anyhow!("invalid control descriptor"))
}
fn list<'a>(v: &'a Json, key: &str) -> Result<&'a Vec<Json>> {
    field(v, key)?
        .as_array()
        .ok_or_else(|| anyhow!("invalid control descriptor"))
}
fn shape(v: &Json, required: &[&str], span: bool) -> Result<()> {
    let object = v
        .as_object()
        .ok_or_else(|| anyhow!("invalid control descriptor"))?;
    ensure!(
        required.iter().all(|k| object.contains_key(*k))
            && object
                .keys()
                .all(|k| required.contains(&k.as_str()) || (span && k == "span")),
        "invalid control fields"
    );
    if let Some(s) = object.get("span") {
        ensure!(s.is_object(), "invalid control span");
    }
    Ok(())
}
fn name(value: &str) -> Result<String> {
    ensure!(
        !value.is_empty() && value.len() <= 1024 && !value.chars().any(char::is_control),
        "invalid control identifier"
    );
    Ok(value.into())
}
fn host_identifier(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"_-.:".contains(&b))
}
fn host_key(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"_-/.:".contains(&b))
        && !value.starts_with('/')
        && !value.ends_with('/')
        && value
            .split('/')
            .all(|s| !s.is_empty() && s != "." && s != "..")
}

#[derive(Clone)]
struct Expr {
    ty: Type,
    kind: ExprKind,
}
#[derive(Clone)]
enum ExprKind {
    Unit,
    Literal(Value),
    Ref(String),
    Binary(String, Arc<Expr>, Arc<Expr>),
    Eq(Type, Arc<Expr>, Arc<Expr>),
    Cast(Arc<Expr>),
    Disclose(Arc<Expr>),
    Select(Arc<Expr>, Arc<Expr>, Arc<Expr>),
    If(Arc<Expr>, Arc<Expr>, Arc<Expr>),
    And(Arc<Expr>, Arc<Expr>),
    Or(Arc<Expr>, Arc<Expr>),
    Hash(String, Arc<Expr>, Arc<Expr>),
    Call(String, Vec<Arc<Expr>>),
    Witness(String),
}
#[derive(Clone)]
enum Stmt {
    Bind(String, Type, Arc<Expr>),
    Evaluate(Arc<Expr>),
    Assert(Arc<Expr>),
    Return(Option<Arc<Expr>>),
    If(Arc<Expr>, Arc<Block>, Arc<Block>),
    Stage(String, String, String, Arc<Expr>),
}
#[derive(Clone, Default)]
struct Block {
    statements: Vec<Stmt>,
    must_return: bool,
    may_return: bool,
}
#[derive(Clone)]
struct Signature {
    parameters: Vec<(String, Type)>,
    result: Type,
}
struct Function {
    signature: Signature,
    body: Arc<Block>,
    calls: Vec<String>,
    nodes: usize,
    depth: usize,
}
struct Plan {
    functions: BTreeMap<String, Arc<Function>>,
    inputs: Vec<(String, String, bool)>,
    witnesses: BTreeMap<String, String>,
    entry: String,
    name: String,
    max_steps: usize,
}
struct Parser<'a> {
    signatures: &'a BTreeMap<String, Signature>,
    witnesses: &'a BTreeMap<String, String>,
    nodes: usize,
    deepest: usize,
    calls: Vec<String>,
}
impl Parser<'_> {
    fn tick(&mut self, depth: usize) -> Result<()> {
        self.nodes += 1;
        self.deepest = self.deepest.max(depth);
        ensure!(
            self.nodes <= MAX_NODES && depth <= MAX_DEPTH,
            "control source resource limit"
        );
        Ok(())
    }
    fn expr(&mut self, v: &Json, env: &BTreeMap<String, Type>, depth: usize) -> Result<Arc<Expr>> {
        self.tick(depth)?;
        let tag = text(v, "tag")?;
        let (ty, kind) = match tag {
            "unit" => {
                shape(v, &["tag"], true)?;
                (Type::Unit, ExprKind::Unit)
            }
            "constant" => {
                shape(v, &["tag", "value"], true)?;
                let x = Value::Native(canonical_field(text(v, "value")?)?);
                (Type::Scalar(x.scalar_type()), ExprKind::Literal(x))
            }
            "bool" => {
                shape(v, &["tag", "value"], true)?;
                let x = Value::Bool(
                    field(v, "value")?
                        .as_bool()
                        .ok_or_else(|| anyhow!("invalid control Boolean"))?,
                );
                (Type::Scalar(ScalarType::Bool), ExprKind::Literal(x))
            }
            "uint" => {
                shape(v, &["tag", "maximum", "value"], true)?;
                let x = scalars::unsigned_literal(text(v, "maximum")?, text(v, "value")?)?;
                (Type::Scalar(x.scalar_type()), ExprKind::Literal(x))
            }
            "reference" => {
                shape(v, &["tag", "name"], true)?;
                let n = name(text(v, "name")?)?;
                (
                    env.get(&n)
                        .ok_or_else(|| anyhow!("unbound control reference"))?
                        .clone(),
                    ExprKind::Ref(n),
                )
            }
            "cast" => {
                shape(v, &["tag", "type", "value"], true)?;
                let target = Type::parse(text(v, "type")?)?;
                scalar_type(&target)?;
                let x = self.expr(field(v, "value")?, env, depth + 1)?;
                scalar_type(&x.ty)?;
                (target, ExprKind::Cast(x))
            }
            "disclose" => {
                shape(v, &["tag", "value"], true)?;
                let x = self.expr(field(v, "value")?, env, depth + 1)?;
                (x.ty.clone(), ExprKind::Disclose(x))
            }
            "binary" | "eq" | "and" | "or" => {
                if tag == "binary" {
                    shape(v, &["tag", "operation", "left", "right"], true)?;
                } else {
                    shape(v, &["tag", "left", "right"], true)?;
                }
                let a = self.expr(field(v, "left")?, env, depth + 1)?;
                let b = self.expr(field(v, "right")?, env, depth + 1)?;
                match tag {
                    "eq" => {
                        scalar_type(&a.ty)?;
                        scalar_type(&b.ty)?;
                        let t = join(&a.ty, &b.ty)?;
                        (Type::Scalar(ScalarType::Bool), ExprKind::Eq(t, a, b))
                    }
                    "and" | "or" => {
                        ensure!(
                            a.ty == Type::Scalar(ScalarType::Bool) && b.ty == a.ty,
                            "control Boolean required"
                        );
                        (
                            a.ty.clone(),
                            if tag == "and" {
                                ExprKind::And(a, b)
                            } else {
                                ExprKind::Or(a, b)
                            },
                        )
                    }
                    _ => {
                        let op = text(v, "operation")?;
                        ensure!(
                            ["add", "sub", "mul"].contains(&op),
                            "invalid control arithmetic"
                        );
                        let lt = scalar_type(&a.ty)?;
                        let rt = scalar_type(&b.ty)?;
                        let t = match (lt, rt) {
                            (ScalarType::Bool, _) | (_, ScalarType::Bool) => {
                                bail!("control Boolean arithmetic")
                            }
                            (ScalarType::Native, _) | (_, ScalarType::Native) => ScalarType::Native,
                            (ScalarType::UInt(m), ScalarType::UInt(n)) => {
                                let maximum = match op {
                                    "add" => m + n,
                                    "sub" => m.clone(),
                                    _ => m * n,
                                };
                                ensure!(maximum <= max_uint(), "control unsigned bound");
                                ScalarType::UInt(maximum)
                            }
                        };
                        (Type::Scalar(t), ExprKind::Binary(op.into(), a, b))
                    }
                }
            }
            "if" | "select" => {
                shape(v, &["tag", "condition", "yes", "no"], true)?;
                let c = self.expr(field(v, "condition")?, env, depth + 1)?;
                ensure!(
                    c.ty == Type::Scalar(ScalarType::Bool),
                    "control Boolean required"
                );
                let a = self.expr(field(v, "yes")?, env, depth + 1)?;
                let b = self.expr(field(v, "no")?, env, depth + 1)?;
                let t = join(&a.ty, &b.ty)?;
                if tag == "select" {
                    scalar_type(&t)?;
                }
                (
                    t,
                    if tag == "if" {
                        ExprKind::If(c, a, b)
                    } else {
                        ExprKind::Select(c, a, b)
                    },
                )
            }
            "poseidon2" => {
                shape(v, &["tag", "domain", "left", "right"], true)?;
                let d = text(v, "domain")?.to_owned();
                canonical_field(&d)?;
                let a = self.expr(field(v, "left")?, env, depth + 1)?;
                let b = self.expr(field(v, "right")?, env, depth + 1)?;
                ensure!(
                    subtype(&a.ty, &Type::Scalar(ScalarType::Native))
                        && subtype(&b.ty, &Type::Scalar(ScalarType::Native)),
                    "control hash scalar types"
                );
                (Type::Scalar(ScalarType::Native), ExprKind::Hash(d, a, b))
            }
            "call" => {
                shape(v, &["tag", "function", "arguments"], true)?;
                let id = text(v, "function")?.to_owned();
                let sig = self
                    .signatures
                    .get(&id)
                    .ok_or_else(|| anyhow!("unknown control function"))?
                    .clone();
                let args = list(v, "arguments")?;
                ensure!(args.len() == sig.parameters.len(), "control call arity");
                let args = args
                    .iter()
                    .map(|x| self.expr(x, env, depth + 1))
                    .collect::<Result<Vec<_>>>()?;
                for (a, (_, t)) in args.iter().zip(&sig.parameters) {
                    ensure!(subtype(&a.ty, t), "control call argument type");
                }
                self.calls.push(id.clone());
                (sig.result, ExprKind::Call(id, args))
            }
            "witness" => {
                shape(v, &["tag", "name", "type"], true)?;
                let n = name(text(v, "name")?)?;
                ensure!(host_identifier(&n), "invalid control witness identifier");
                let t = text(v, "type")?;
                ensure!(
                    self.witnesses.get(&n).map(String::as_str) == Some(t),
                    "control witness schema mismatch"
                );
                (Type::Scalar(ScalarType::parse(t)?), ExprKind::Witness(n))
            }
            _ => bail!("unsupported control expression"),
        };
        Ok(Arc::new(Expr { ty, kind }))
    }
    fn block(
        &mut self,
        values: &[Json],
        initial: &BTreeMap<String, Type>,
        result: &Type,
        depth: usize,
    ) -> Result<Arc<Block>> {
        let mut env = initial.clone();
        let mut block = Block::default();
        for value in values {
            self.tick(depth)?;
            let tag = text(value, "tag")?;
            let stmt = match tag {
                "bind" => {
                    shape(value, &["tag", "name", "type", "value"], true)?;
                    let n = name(text(value, "name")?)?;
                    ensure!(!env.contains_key(&n), "duplicate control local");
                    let t = Type::parse(text(value, "type")?)?;
                    let x = self.expr(field(value, "value")?, &env, depth + 1)?;
                    ensure!(subtype(&x.ty, &t), "control binding type");
                    env.insert(n.clone(), t.clone());
                    Stmt::Bind(n, t, x)
                }
                "evaluate" => {
                    shape(value, &["tag", "value"], true)?;
                    Stmt::Evaluate(self.expr(field(value, "value")?, &env, depth + 1)?)
                }
                "assert" => {
                    shape(value, &["tag", "condition"], true)?;
                    let x = self.expr(field(value, "condition")?, &env, depth + 1)?;
                    ensure!(
                        x.ty == Type::Scalar(ScalarType::Bool),
                        "control assertion requires Boolean"
                    );
                    Stmt::Assert(x)
                }
                "return" => {
                    shape(value, &["tag", "value"], true)?;
                    let x = if field(value, "value")?.is_null() {
                        None
                    } else {
                        Some(self.expr(field(value, "value")?, &env, depth + 1)?)
                    };
                    ensure!(
                        subtype(
                            &x.as_ref().map(|x| x.ty.clone()).unwrap_or(Type::Unit),
                            result
                        ),
                        "control return type"
                    );
                    block.must_return = true;
                    block.may_return = true;
                    Stmt::Return(x)
                }
                "if" => {
                    shape(value, &["tag", "condition", "yes", "no"], true)?;
                    let c = self.expr(field(value, "condition")?, &env, depth + 1)?;
                    ensure!(
                        c.ty == Type::Scalar(ScalarType::Bool),
                        "control Boolean required"
                    );
                    let yes = self.block(list(value, "yes")?, &env, result, depth + 1)?;
                    let no = self.block(list(value, "no")?, &env, result, depth + 1)?;
                    block.must_return |= yes.must_return && no.must_return;
                    block.may_return |= yes.may_return || no.may_return;
                    Stmt::If(c, yes, no)
                }
                "stage" => {
                    shape(value, &["tag", "capability", "key", "type", "value"], true)?;
                    let t = text(value, "type")?.to_owned();
                    let target = Type::Scalar(ScalarType::parse(&t)?);
                    let x = self.expr(field(value, "value")?, &env, depth + 1)?;
                    ensure!(subtype(&x.ty, &target), "control private stage type");
                    {
                        let cap = text(value, "capability")?;
                        let key = text(value, "key")?;
                        ensure!(
                            host_identifier(cap) && host_key(key),
                            "invalid control stage descriptor"
                        );
                        Stmt::Stage(cap.into(), key.into(), t, x)
                    }
                }
                _ => bail!("unsupported control statement"),
            };
            block.statements.push(stmt);
        }
        Ok(Arc::new(block))
    }
}
fn parse_parameters(v: &Json) -> Result<Vec<(String, Type)>> {
    let values = list(v, "parameters")?;
    ensure!(values.len() <= MAX_ARGUMENTS, "control parameter limit");
    let mut names = BTreeSet::new();
    values
        .iter()
        .map(|v| {
            shape(v, &["name", "type"], false)?;
            let n = name(text(v, "name")?)?;
            ensure!(names.insert(n.clone()), "duplicate control parameter");
            let t = Type::Scalar(ScalarType::parse(text(v, "type")?)?);
            Ok((n, t))
        })
        .collect()
}
fn raw_preflight(value: &Json) -> Result<()> {
    let mut work = vec![(value, 0usize)];
    let mut nodes = 0usize;
    let mut string_bytes = 0usize;
    while let Some((value, depth)) = work.pop() {
        nodes += 1;
        ensure!(
            nodes <= 131072 && depth <= 256,
            "control JSON resource limit"
        );
        match value {
            Json::Array(values) => {
                ensure!(
                    work.len() + values.len() <= 131072,
                    "control JSON resource limit"
                );
                work.extend(values.iter().map(|v| (v, depth + 1)));
            }
            Json::Object(values) => {
                ensure!(
                    work.len() + values.len() <= 131072,
                    "control JSON resource limit"
                );
                for (key, value) in values {
                    string_bytes = string_bytes.saturating_add(key.len());
                    work.push((value, depth + 1));
                }
            }
            Json::String(s) => string_bytes = string_bytes.saturating_add(s.len()),
            _ => {}
        }
        ensure!(string_bytes <= MAX_BYTES, "control JSON byte limit");
    }
    Ok(())
}

impl Plan {
    fn parse(v: &Json) -> Result<Self> {
        raw_preflight(v)?;
        ensure!(
            serde_json::to_vec(v)?.len() <= MAX_BYTES,
            "control plan byte limit"
        );
        shape(
            v,
            &[
                "schemaVersion",
                "kind",
                "name",
                "inputs",
                "witnesses",
                "functions",
                "entry",
                "limits",
            ],
            false,
        )?;
        ensure!(
            field(v, "schemaVersion")?.as_u64() == Some(1) && text(v, "kind")? == "host-control",
            "unsupported control schema"
        );
        shape(field(v, "limits")?, &["maxSteps"], false)?;
        let max_steps = field(field(v, "limits")?, "maxSteps")?
            .as_u64()
            .ok_or_else(|| anyhow!("invalid control fuel"))?;
        ensure!(
            max_steps > 0 && max_steps <= MAX_STEPS as u64,
            "control execution policy limit"
        );
        let mut inputs = Vec::new();
        let mut names = BTreeSet::new();
        ensure!(
            list(v, "inputs")?.len() <= MAX_ARGUMENTS,
            "control input limit"
        );
        for input in list(v, "inputs")? {
            shape(input, &["name", "type", "visibility"], true)?;
            let n = name(text(input, "name")?)?;
            ensure!(names.insert(n.clone()), "duplicate control input");
            let t = text(input, "type")?.to_owned();
            ScalarType::parse(&t)?;
            let visibility = text(input, "visibility")?;
            ensure!(
                ["public", "private"].contains(&visibility),
                "invalid control visibility"
            );
            inputs.push((n, t, visibility == "private"));
        }
        let mut witnesses = BTreeMap::new();
        ensure!(
            list(v, "witnesses")?.len() <= MAX_WITNESSES,
            "control witness limit"
        );
        for witness in list(v, "witnesses")? {
            shape(witness, &["name", "type"], true)?;
            let n = name(text(witness, "name")?)?;
            ensure!(host_identifier(&n), "invalid control witness identifier");
            let t = text(witness, "type")?.to_owned();
            ScalarType::parse(&t)?;
            ensure!(
                witnesses.insert(n, t).is_none(),
                "duplicate control witness"
            );
        }
        let raw = list(v, "functions")?;
        ensure!(
            !raw.is_empty() && raw.len() <= MAX_FUNCTIONS,
            "control function limit"
        );
        let mut signatures = BTreeMap::new();
        for f in raw {
            shape(f, &["id", "name", "parameters", "resultType", "body"], true)?;
            let id = name(text(f, "id")?)?;
            name(text(f, "name")?)?;
            let signature = Signature {
                parameters: parse_parameters(f)?,
                result: Type::parse(text(f, "resultType")?)?,
            };
            ensure!(
                signatures.insert(id, signature).is_none(),
                "duplicate control function"
            );
        }
        let entry = text(v, "entry")?.to_owned();
        let sig = signatures
            .get(&entry)
            .ok_or_else(|| anyhow!("unknown control entry"))?;
        ensure!(sig.parameters.len() == inputs.len(), "control entry arity");
        for ((_, t, _), (_, expected)) in inputs.iter().zip(&sig.parameters) {
            ensure!(
                subtype(&Type::Scalar(ScalarType::parse(t)?), expected),
                "control entry type"
            );
        }
        let mut functions = BTreeMap::new();
        let mut total = 0;
        for f in raw {
            let id = text(f, "id")?.to_owned();
            let signature = signatures[&id].clone();
            let env = signature.parameters.iter().cloned().collect();
            let mut parser = Parser {
                signatures: &signatures,
                witnesses: &witnesses,
                nodes: 0,
                deepest: 0,
                calls: vec![],
            };
            let body = parser.block(list(f, "body")?, &env, &signature.result, 1)?;
            ensure!(
                signature.result == Type::Unit || body.must_return,
                "control fall-through returns unit"
            );
            total += parser.nodes;
            ensure!(total <= MAX_NODES, "control source node limit");
            functions.insert(
                id,
                Arc::new(Function {
                    nodes: 3 * (parser.nodes + signature.parameters.len() + 2),
                    depth: 3
                        * (body.statements.len() + parser.deepest + signature.parameters.len() + 2),
                    signature,
                    body,
                    calls: parser.calls,
                }),
            );
        }
        fn graph(
            id: &str,
            functions: &BTreeMap<String, Arc<Function>>,
            stack: &mut BTreeSet<String>,
            cache: &mut BTreeMap<String, (usize, usize, usize)>,
            visits: &mut usize,
        ) -> Result<(usize, usize, usize)> {
            *visits += 1;
            ensure!(*visits <= 65536, "control call analysis limit");
            ensure!(!stack.contains(id), "recursive control call");
            if let Some(c) = cache.get(id) {
                ensure!(stack.len() + c.2 <= 64, "control call depth limit");
                return Ok(*c);
            };
            ensure!(stack.len() < 64, "control call depth limit");
            stack.insert(id.into());
            let f = &functions[id];
            let mut nodes = f.nodes;
            let mut depth = 0;
            let mut calls = 0;
            for child in &f.calls {
                let (n, d, c) = graph(child, functions, stack, cache, visits)?;
                nodes = nodes.saturating_add(n).min(65537);
                depth = depth.max(d);
                calls = calls.max(c);
                ensure!(nodes <= 65536, "control expanded node limit");
            }
            stack.remove(id);
            depth = f.depth.saturating_add(depth).min(257);
            ensure!(depth <= 256 && calls < 64, "control expanded depth limit");
            let answer = (nodes, depth, calls + 1);
            cache.insert(id.into(), answer);
            Ok(answer)
        }
        graph(
            &entry,
            &functions,
            &mut BTreeSet::new(),
            &mut BTreeMap::new(),
            &mut 0,
        )?;
        Ok(Self {
            functions,
            inputs,
            witnesses,
            entry,
            name: name(text(v, "name")?)?,
            max_steps: max_steps as usize,
        })
    }
}

// Unknown is distinct from known unit. Constants never invoke host effects.
type Known = Option<Option<Value>>;
type Constants = BTreeMap<String, Known>;
fn known_bool(value: &Known) -> Option<bool> {
    match value {
        Some(Some(Value::Bool(v))) => Some(*v),
        _ => None,
    }
}
fn known_cast(ty: &Type, value: Known) -> Known {
    match (ty, value) {
        (_, None) => None,
        (Type::Unit, Some(None)) => Some(None),
        (Type::Scalar(ty), Some(Some(value))) => value.cast(ty).ok().map(Some),
        _ => None,
    }
}
fn known_merge(values: Vec<Known>) -> Known {
    let mut it = values.into_iter();
    let first = it.next()?;
    if it.all(|v| v == first) { first } else { None }
}
fn known_environment(env: &Env) -> Constants {
    env.iter()
        .map(|(n, v)| (n.clone(), v.known.clone()))
        .collect()
}
fn arithmetic(op: &str, ty: &Type, a: Value, b: Value) -> Result<Value> {
    match scalar_type(ty)? {
        ScalarType::Native => {
            let a = a.cast(&ScalarType::Native)?.field_encoding()?;
            let b = b.cast(&ScalarType::Native)?.field_encoding()?;
            Ok(Value::Native(match op {
                "add" => a + b,
                "sub" => a - b,
                _ => a * b,
            }))
        }
        ScalarType::UInt(m) => scalars::unsigned_arithmetic(
            match op {
                "add" => scalars::UnsignedOp::Add,
                "sub" => scalars::UnsignedOp::Sub,
                _ => scalars::UnsignedOp::Mul,
            },
            a,
            b,
            &m.to_str_radix(10),
        ),
        _ => bail!("control arithmetic type"),
    }
}
struct AbstractFlow {
    returns: Vec<Known>,
    falls: bool,
}
struct Abstractor<'a> {
    functions: &'a BTreeMap<String, Arc<Function>>,
    fuel: &'a mut usize,
}
impl Abstractor<'_> {
    fn tick(&mut self) -> Result<()> {
        ensure!(*self.fuel > 0, "control abstract analysis fuel");
        *self.fuel -= 1;
        Ok(())
    }
    fn expression(&mut self, expr: &Expr, env: &Constants) -> Result<Known> {
        self.tick()?;
        Ok(match &expr.kind {
            ExprKind::Unit => Some(None),
            ExprKind::Literal(v) => Some(Some(v.clone())),
            ExprKind::Ref(n) => env.get(n).cloned().unwrap_or(None),
            ExprKind::Cast(x) => known_cast(&expr.ty, self.expression(x, env)?),
            ExprKind::Disclose(x) => self.expression(x, env)?,
            ExprKind::Binary(op, a, b) => {
                let a = self.expression(a, env)?;
                let b = self.expression(b, env)?;
                match (a, b) {
                    (Some(Some(a)), Some(Some(b))) => arithmetic(op, &expr.ty, a, b).ok().map(Some),
                    _ => None,
                }
            }
            ExprKind::Eq(ty, a, b) => {
                let a = known_cast(ty, self.expression(a, env)?);
                let b = known_cast(ty, self.expression(b, env)?);
                match (a, b) {
                    (Some(a), Some(b)) => Some(Some(Value::Bool(a == b))),
                    _ => None,
                }
            }
            ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                let or = matches!(expr.kind, ExprKind::Or(_, _));
                let a = self.expression(a, env)?;
                match known_bool(&a) {
                    Some(v) if v == or => Some(Some(Value::Bool(or))),
                    Some(_) => self.expression(b, env)?,
                    None => {
                        let b = self.expression(b, env)?;
                        if known_bool(&b) == Some(or) {
                            Some(Some(Value::Bool(or)))
                        } else {
                            None
                        }
                    }
                }
            }
            ExprKind::If(c, a, b) | ExprKind::Select(c, a, b) => {
                let c = self.expression(c, env)?;
                match known_bool(&c) {
                    Some(v) => known_cast(&expr.ty, self.expression(if v { a } else { b }, env)?),
                    None => known_merge(vec![
                        known_cast(&expr.ty, self.expression(a, env)?),
                        known_cast(&expr.ty, self.expression(b, env)?),
                    ]),
                }
            }
            ExprKind::Call(id, args) => {
                let f = self.functions[id].clone();
                let mut local = BTreeMap::new();
                for ((n, t), a) in f.signature.parameters.iter().zip(args) {
                    local.insert(n.clone(), known_cast(t, self.expression(a, env)?));
                }
                let mut flow = self.body(&f.body, &local, &f.signature.result)?;
                if flow.falls {
                    flow.returns.push(Some(None));
                }
                known_merge(flow.returns)
            }
            ExprKind::Witness(_) | ExprKind::Hash(_, _, _) => None,
        })
    }
    fn body(&mut self, body: &Block, initial: &Constants, result: &Type) -> Result<AbstractFlow> {
        let mut env = initial.clone();
        let mut flow = AbstractFlow {
            returns: vec![],
            falls: true,
        };
        for stmt in &body.statements {
            if !flow.falls {
                break;
            }
            self.tick()?;
            match stmt {
                Stmt::Bind(n, t, x) => {
                    let value = known_cast(t, self.expression(x, &env)?);
                    env.insert(n.clone(), value);
                }
                Stmt::Return(x) => {
                    let value = match x {
                        Some(x) => self.expression(x, &env)?,
                        None => Some(None),
                    };
                    flow.returns.push(known_cast(result, value));
                    flow.falls = false;
                }
                Stmt::If(c, yes, no) => {
                    let condition = self.expression(c, &env)?;
                    let branches = match known_bool(&condition) {
                        Some(true) => vec![yes],
                        Some(false) => vec![no],
                        None => vec![yes, no],
                    };
                    let mut falls = false;
                    for branch in branches {
                        let inner = self.body(branch, &env, result)?;
                        falls |= inner.falls;
                        flow.returns.extend(inner.returns);
                    }
                    flow.falls = falls;
                }
                Stmt::Evaluate(_) | Stmt::Assert(_) | Stmt::Stage(_, _, _, _) => {}
            }
        }
        Ok(flow)
    }
}

#[derive(Clone)]
struct Tracked {
    value: Option<Value>,
    taint: bool,
    known: Known,
}
impl Tracked {
    fn unit() -> Self {
        Self {
            value: None,
            taint: false,
            known: Some(None),
        }
    }
    fn scalar(value: Value, taint: bool) -> Self {
        let known = if taint {
            None
        } else {
            Some(Some(value.clone()))
        };
        Self {
            value: Some(value),
            taint,
            known,
        }
    }
    fn boolean(&self) -> Result<bool> {
        match self.value {
            Some(Value::Bool(b)) => Ok(b),
            _ => bail!("control Boolean required"),
        }
    }
}
type Env = Arc<BTreeMap<String, Tracked>>;
enum Task {
    Eval(Arc<Expr>, Env),
    Unary(Type, bool),
    Merge(Type, bool),
    Binary(String, Type),
    Eq(Type),
    Hash(String),
    EagerSelect(Type),
    Choose(Arc<Expr>, Arc<Expr>, Type, Env, Arc<Expr>),
    Short(bool, Arc<Expr>, Env),
    Args(String, Vec<Arc<Expr>>, usize, Vec<Tracked>, Env),
    ArgValue(String, Vec<Arc<Expr>>, usize, Vec<Tracked>, Env),
    Body(Arc<Block>, usize, Env, bool, Type),
    Bind(String, Type, Arc<Block>, usize, Env, bool, Type, Arc<Expr>),
    Discard,
    Assert,
    Return(Type, bool),
    Boundary(Type, bool),
    Finish,
    Branch(
        Arc<Block>,
        Arc<Block>,
        Arc<Block>,
        usize,
        Env,
        bool,
        Type,
        Arc<Expr>,
    ),
    Stage(String, String, String),
}
pub(crate) fn wipe_json(value: &mut Json) {
    match value {
        Json::String(s) => s.zeroize(),
        Json::Array(v) => v.iter_mut().for_each(wipe_json),
        Json::Object(v) => v.values_mut().for_each(wipe_json),
        _ => {}
    }
}

#[derive(Clone, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Response {
    pub abi_version: u32,
    pub request_id: u64,
    pub operation: String,
    pub capability: String,
    pub schema: String,
    pub value: Json,
}
impl Drop for Response {
    fn drop(&mut self) {
        wipe_json(&mut self.value);
    }
}
struct Pending {
    id: u64,
    name: String,
    ty: String,
    request: Json,
}
enum Phase {
    Ready,
    Waiting,
    Complete(Json),
    Failed,
    Cancelled,
}
/// A source-only invocation. No acceptance/commit notices or native proof API is exposed.
pub struct Session {
    plan: Plan,
    host: Option<host::Runtime>,
    tasks: Vec<Task>,
    values: Vec<Tracked>,
    pending: Option<Pending>,
    phase: Phase,
    next_id: u64,
    remaining: usize,
    trace: Vec<String>,
    invocation_writes: BTreeMap<String, Json>,
    continuation_taint: bool,
}
impl Session {
    pub fn from_json(
        plan: Json,
        inputs: BTreeMap<String, Json>,
        context: host::Context,
    ) -> Result<Self> {
        let plan = Plan::parse(&plan)?;
        ensure!(
            inputs.len() == plan.inputs.len(),
            "control input schema mismatch"
        );
        ensure!(
            plan.witnesses
                .keys()
                .all(|n| context.providers.iter().any(|p| &p.input == n)),
            "control witness requires registered provider"
        );
        let host = host::Runtime::new(
            context,
            &plan.witnesses,
            plan.name.clone(),
            plan.entry.clone(),
        )?;
        let signature = &plan.functions[&plan.entry].signature;
        let mut env = BTreeMap::new();
        for ((input, ty, private), (parameter, target)) in
            plan.inputs.iter().zip(&signature.parameters)
        {
            let value = input_value(
                ty,
                inputs
                    .get(input)
                    .ok_or_else(|| anyhow!("missing control input"))?,
            )?;
            env.insert(
                parameter.clone(),
                target.coerce(Tracked::scalar(value, *private))?,
            );
        }
        let function = &plan.functions[&plan.entry];
        let tasks = vec![
            Task::Finish,
            Task::Boundary(signature.result.clone(), false),
            Task::Body(
                function.body.clone(),
                0,
                Arc::new(env),
                false,
                signature.result.clone(),
            ),
        ];
        let remaining = plan.max_steps;
        Ok(Self {
            plan,
            host: Some(host),
            tasks,
            values: vec![],
            pending: None,
            phase: Phase::Ready,
            next_id: 0,
            remaining,
            trace: vec![],
            invocation_writes: BTreeMap::new(),
            continuation_taint: false,
        })
    }
    fn pop(&mut self) -> Result<Tracked> {
        self.values
            .pop()
            .ok_or_else(|| anyhow!("invalid control machine state"))
    }
    fn clear_writes(&mut self) {
        for (mut key, mut value) in std::mem::take(&mut self.invocation_writes) {
            key.zeroize();
            wipe_json(&mut value);
        }
    }
    fn reject(&mut self) {
        self.clear_writes();
        self.tasks.clear();
        self.values.clear();
        self.pending = None;
        if let Some(mut host) = self.host.take() {
            let _ = host.cancel();
        }
        self.phase = Phase::Failed;
    }
    pub fn private_trace(&self) -> Json {
        json!({"protocolVersion":1,"events":self.trace})
    }
    pub fn private_request(&self) -> Result<Json> {
        ensure!(
            matches!(self.phase, Phase::Waiting),
            "invalid control lifecycle state"
        );
        let mut request = self
            .host
            .as_ref()
            .ok_or_else(|| anyhow!("invalid control lifecycle state"))?
            .private_arguments()?;
        request["invocationWrites"] = json!(self.invocation_writes);
        Ok(request)
    }
    pub fn stage(&mut self, stage: host::Stage) -> Result<()> {
        ensure!(
            matches!(self.phase, Phase::Ready | Phase::Waiting),
            "invalid control lifecycle state"
        );
        let key = stage.key.clone();
        let mut value = json!({"type":stage.ty,"value":stage.value});
        let staged = self
            .host
            .as_mut()
            .ok_or_else(|| anyhow!("invalid control lifecycle state"))?
            .stage(stage);
        if let Err(error) = staged {
            wipe_json(&mut value);
            return Err(error.into());
        }
        if let Some(mut old) = self.invocation_writes.insert(key, value) {
            wipe_json(&mut old);
        }
        self.trace.push("stage".into());
        Ok(())
    }
    pub fn cancel(&mut self) -> Result<Json> {
        if !matches!(self.phase, Phase::Cancelled) {
            self.clear_writes();
            self.tasks.clear();
            self.values.clear();
            self.pending = None;
            if let Some(mut host) = self.host.take() {
                host.cancel()?;
            }
            self.phase = Phase::Cancelled;
        }
        Ok(json!({"abiVersion":1,"status":"cancelled"}))
    }
    pub fn resume(&mut self, response: Response) -> Result<Json> {
        ensure!(
            matches!(self.phase, Phase::Waiting),
            "invalid control lifecycle state"
        );
        let pending = self
            .pending
            .as_ref()
            .ok_or_else(|| anyhow!("invalid control lifecycle state"))?;
        ensure!(
            response.abi_version == 1 && response.request_id == pending.id,
            "invalid control host response"
        );
        let value = input_value(&pending.ty, &response.value)?;
        self.host
            .as_mut()
            .ok_or_else(|| anyhow!("invalid control lifecycle state"))?
            .finish_input(
                &pending.name,
                pending.id,
                Some(&response.operation),
                Some(&response.capability),
                Some(&response.schema),
                &response.value,
            )?;
        self.values.push(Tracked::scalar(value, true));
        self.pending = None;
        self.phase = Phase::Ready;
        Ok(json!({"abiVersion":1,"status":"ready"}))
    }
    pub fn advance(&mut self) -> Result<Json> {
        match &self.phase {
            Phase::Waiting => {
                return Ok(
                    json!({"abiVersion":1,"status":"need_host","request":self.pending.as_ref().ok_or_else(||anyhow!("invalid control pending state"))?.request}),
                );
            }
            Phase::Complete(v) => return Ok(v.clone()),
            Phase::Failed => {
                return Ok(
                    json!({"abiVersion":1,"status":"failed","error":{"code":"execution_rejected"}}),
                );
            }
            Phase::Cancelled => return Ok(json!({"abiVersion":1,"status":"cancelled"})),
            Phase::Ready => {}
        }
        while let Some(task) = self.tasks.pop() {
            if self.remaining == 0 {
                self.reject();
                return self.advance();
            }
            self.remaining -= 1;
            if self.step(task).is_err() {
                self.reject();
                return self.advance();
            }
            if !matches!(self.phase, Phase::Ready) {
                return self.advance();
            }
        }
        self.reject();
        self.advance()
    }
    fn known_expression(&mut self, expression: &Expr, env: &Env) -> Result<Known> {
        Abstractor {
            functions: &self.plan.functions,
            fuel: &mut self.remaining,
        }
        .expression(expression, &known_environment(env))
    }
    fn step(&mut self, task: Task) -> Result<()> {
        match task {
            Task::Eval(expr, env) => match &expr.kind {
                ExprKind::Unit => self.values.push(Tracked::unit()),
                ExprKind::Literal(v) => self.values.push(Tracked::scalar(v.clone(), false)),
                ExprKind::Ref(n) => self.values.push(
                    env.get(n)
                        .ok_or_else(|| anyhow!("unbound control value"))?
                        .clone(),
                ),
                ExprKind::Cast(x) | ExprKind::Disclose(x) => {
                    self.tasks.push(Task::Unary(
                        expr.ty.clone(),
                        matches!(expr.kind, ExprKind::Disclose(_)),
                    ));
                    self.tasks.push(Task::Eval(x.clone(), env));
                }
                ExprKind::Binary(op, a, b) => {
                    self.tasks.push(Task::Binary(op.clone(), expr.ty.clone()));
                    self.tasks.push(Task::Eval(b.clone(), env.clone()));
                    self.tasks.push(Task::Eval(a.clone(), env));
                }
                ExprKind::Eq(t, a, b) => {
                    self.tasks.push(Task::Eq(t.clone()));
                    self.tasks.push(Task::Eval(b.clone(), env.clone()));
                    self.tasks.push(Task::Eval(a.clone(), env));
                }
                ExprKind::Hash(d, a, b) => {
                    self.tasks.push(Task::Hash(d.clone()));
                    self.tasks.push(Task::Eval(b.clone(), env.clone()));
                    self.tasks.push(Task::Eval(a.clone(), env));
                }
                ExprKind::Select(c, a, b) => {
                    self.tasks.push(Task::EagerSelect(expr.ty.clone()));
                    self.tasks.push(Task::Eval(b.clone(), env.clone()));
                    self.tasks.push(Task::Eval(a.clone(), env.clone()));
                    self.tasks.push(Task::Eval(c.clone(), env));
                }
                ExprKind::If(c, a, b) => {
                    self.tasks.push(Task::Choose(
                        a.clone(),
                        b.clone(),
                        expr.ty.clone(),
                        env.clone(),
                        c.clone(),
                    ));
                    self.tasks.push(Task::Eval(c.clone(), env));
                }
                ExprKind::And(a, b) | ExprKind::Or(a, b) => {
                    self.tasks.push(Task::Short(
                        matches!(expr.kind, ExprKind::Or(_, _)),
                        b.clone(),
                        env.clone(),
                    ));
                    self.tasks.push(Task::Eval(a.clone(), env));
                }
                ExprKind::Call(id, args) => {
                    self.tasks
                        .push(Task::Args(id.clone(), args.clone(), 0, vec![], env))
                }
                ExprKind::Witness(n) => {
                    self.next_id = self
                        .next_id
                        .checked_add(1)
                        .ok_or_else(|| anyhow!("control request limit"))?;
                    let request = self
                        .host
                        .as_mut()
                        .ok_or_else(|| anyhow!("invalid control host state"))?
                        .begin_input(n, self.next_id)?
                        .ok_or_else(|| anyhow!("control witness requires provider"))?;
                    self.pending = Some(Pending {
                        id: self.next_id,
                        name: n.clone(),
                        ty: self.plan.witnesses[n].clone(),
                        request,
                    });
                    self.trace.push(format!("witness:{n}"));
                    self.phase = Phase::Waiting;
                }
            },
            Task::Unary(ty, disclose) => {
                let value = self.pop()?;
                let mut value = ty.coerce(value)?;
                if disclose {
                    value.taint = false;
                    value.known = Some(value.value.clone());
                }
                self.values.push(value);
            }
            Task::Merge(ty, taint) => {
                let value = self.pop()?;
                let mut value = ty.coerce(value)?;
                value.taint |= taint;
                self.values.push(value);
            }
            Task::Binary(op, ty) => {
                let b = self.pop()?;
                let a = self.pop()?;
                let taint = a.taint || b.taint;
                let a = a.value.ok_or_else(|| anyhow!("control scalar required"))?;
                let b = b.value.ok_or_else(|| anyhow!("control scalar required"))?;
                let value = match scalar_type(&ty)? {
                    ScalarType::Native => {
                        let a = a.cast(&ScalarType::Native)?.field_encoding()?;
                        let b = b.cast(&ScalarType::Native)?.field_encoding()?;
                        Value::Native(match op.as_str() {
                            "add" => a + b,
                            "sub" => a - b,
                            _ => a * b,
                        })
                    }
                    ScalarType::UInt(m) => scalars::unsigned_arithmetic(
                        match op.as_str() {
                            "add" => scalars::UnsignedOp::Add,
                            "sub" => scalars::UnsignedOp::Sub,
                            _ => scalars::UnsignedOp::Mul,
                        },
                        a,
                        b,
                        &m.to_str_radix(10),
                    )?,
                    _ => bail!("control arithmetic type"),
                };
                self.values.push(Tracked::scalar(value, taint));
            }
            Task::Eq(ty) => {
                let b = self.pop()?;
                let a = self.pop()?;
                let taint = a.taint || b.taint;
                let a = ty.coerce(a)?;
                let b = ty.coerce(b)?;
                self.values
                    .push(Tracked::scalar(Value::Bool(a.value == b.value), taint));
            }
            Task::Hash(domain) => {
                let b = self.pop()?;
                let a = self.pop()?;
                let taint = a.taint || b.taint;
                let a = a
                    .value
                    .ok_or_else(|| anyhow!("control hash scalar"))?
                    .field_encoding()?;
                let b = b
                    .value
                    .ok_or_else(|| anyhow!("control hash scalar"))?
                    .field_encoding()?;
                let value =
                    transient_crypto::hash::transient_hash(&[canonical_field(&domain)?, a, b]);
                self.values
                    .push(Tracked::scalar(Value::Native(value), taint));
            }
            Task::EagerSelect(ty) => {
                let no = self.pop()?;
                let yes = self.pop()?;
                let c = self.pop()?;
                let bit = c.boolean()?;
                let taint = c.taint || yes.taint || no.taint;
                let mut value = ty.coerce(if bit { yes } else { no })?;
                value.taint = taint;
                self.values.push(value);
            }
            Task::Choose(yes, no, ty, env, condition) => {
                let c = self.pop()?;
                let known = self.known_expression(&condition, &env)?;
                self.tasks
                    .push(Task::Merge(ty, c.taint && known_bool(&known).is_none()));
                self.tasks
                    .push(Task::Eval(if c.boolean()? { yes } else { no }, env));
            }
            Task::Short(or, right, env) => {
                let left = self.pop()?;
                if left.boolean()? == or {
                    self.values.push(left);
                } else {
                    self.tasks
                        .push(Task::Merge(Type::Scalar(ScalarType::Bool), left.taint));
                    self.tasks.push(Task::Eval(right, env));
                }
            }
            Task::Args(id, args, index, values, env) => {
                if index < args.len() {
                    self.tasks
                        .push(Task::ArgValue(id, args.clone(), index, values, env.clone()));
                    self.tasks.push(Task::Eval(args[index].clone(), env));
                } else {
                    let function = self
                        .plan
                        .functions
                        .get(&id)
                        .ok_or_else(|| anyhow!("unknown control function"))?;
                    let mut local = BTreeMap::new();
                    for ((n, t), v) in function.signature.parameters.iter().zip(values) {
                        local.insert(n.clone(), t.coerce(v)?);
                    }
                    self.tasks.push(Task::Boundary(
                        function.signature.result.clone(),
                        self.continuation_taint,
                    ));
                    self.continuation_taint = false;
                    self.tasks.push(Task::Body(
                        function.body.clone(),
                        0,
                        Arc::new(local),
                        false,
                        function.signature.result.clone(),
                    ));
                }
            }
            Task::ArgValue(id, args, index, mut values, env) => {
                let mut value = self.pop()?;
                value.known = self.known_expression(&args[index], &env)?;
                values.push(value);
                self.tasks
                    .push(Task::Args(id, args, index + 1, values, env));
            }
            Task::Body(body, index, env, control, result) => {
                if let Some(stmt) = body.statements.get(index) {
                    match stmt {
                        Stmt::Bind(n, t, x) => {
                            self.tasks.push(Task::Bind(
                                n.clone(),
                                t.clone(),
                                body.clone(),
                                index + 1,
                                env.clone(),
                                control,
                                result,
                                x.clone(),
                            ));
                            self.tasks.push(Task::Eval(x.clone(), env));
                        }
                        Stmt::Evaluate(x) => {
                            self.tasks.push(Task::Body(
                                body.clone(),
                                index + 1,
                                env.clone(),
                                control,
                                result,
                            ));
                            self.tasks.push(Task::Discard);
                            self.tasks.push(Task::Eval(x.clone(), env));
                        }
                        Stmt::Assert(x) => {
                            self.tasks.push(Task::Body(
                                body.clone(),
                                index + 1,
                                env.clone(),
                                control,
                                result,
                            ));
                            self.tasks.push(Task::Assert);
                            self.tasks.push(Task::Eval(x.clone(), env));
                        }
                        Stmt::Return(x) => {
                            self.tasks.push(Task::Return(result, control));
                            if let Some(x) = x {
                                self.tasks.push(Task::Eval(x.clone(), env));
                            } else {
                                self.values.push(Tracked::unit());
                            }
                        }
                        Stmt::If(c, yes, no) => {
                            self.tasks.push(Task::Branch(
                                yes.clone(),
                                no.clone(),
                                body.clone(),
                                index + 1,
                                env.clone(),
                                control,
                                result,
                                c.clone(),
                            ));
                            self.tasks.push(Task::Eval(c.clone(), env));
                        }
                        Stmt::Stage(cap, key, ty, x) => {
                            self.tasks.push(Task::Body(
                                body.clone(),
                                index + 1,
                                env.clone(),
                                control,
                                result,
                            ));
                            self.tasks
                                .push(Task::Stage(cap.clone(), key.clone(), ty.clone()));
                            self.tasks.push(Task::Eval(x.clone(), env));
                        }
                    }
                }
            }
            Task::Bind(n, ty, body, index, env, control, result, expression) => {
                let mut value = self.pop()?;
                value.known = self.known_expression(&expression, &env)?;
                let value = ty.coerce(value)?;
                let mut local = (*env).clone();
                local.insert(n, value);
                self.tasks
                    .push(Task::Body(body, index, Arc::new(local), control, result));
            }
            Task::Discard => {
                self.pop()?;
            }
            Task::Assert => {
                ensure!(self.pop()?.boolean()?, "control assertion failed");
            }
            Task::Return(ty, control) => {
                let mut value = ty.coerce(self.pop()?)?;
                value.taint |= control || self.continuation_taint;
                while let Some(task) = self.tasks.pop() {
                    if let Task::Boundary(_, outer_taint) = task {
                        self.continuation_taint = outer_taint;
                        self.values.push(value);
                        return Ok(());
                    }
                }
                bail!("invalid control return boundary")
            }
            Task::Boundary(ty, outer_taint) => {
                let mut value = Tracked::unit();
                value.taint = self.continuation_taint;
                self.continuation_taint = outer_taint;
                self.values.push(ty.coerce(value)?);
            }
            Task::Finish => {
                let value = self.pop()?;
                ensure!(
                    value.value.is_none() || !value.taint,
                    "undisclosed control output"
                );
                let actual = value
                    .value
                    .as_ref()
                    .map(|v| Type::Scalar(v.scalar_type()))
                    .unwrap_or(Type::Unit);
                ensure!(
                    actual == self.plan.functions[&self.plan.entry].signature.result,
                    "control exported value type mismatch"
                );
                let result = value.value.map(|v| v.public_json()).unwrap_or(Json::Null);
                self.phase =
                    Phase::Complete(json!({"abiVersion":1,"status":"completed","result":result}));
                self.tasks.clear();
                self.values.clear();
            }
            Task::Branch(yes, no, rest, index, env, control, result, condition) => {
                let c = self.pop()?;
                let constants = known_environment(&env);
                let mut abstractor = Abstractor {
                    functions: &self.plan.functions,
                    fuel: &mut self.remaining,
                };
                let known = abstractor.expression(&condition, &constants)?;
                let guard = c.taint && known_bool(&known).is_none();
                let may_return = !abstractor
                    .body(&yes, &constants, &result)?
                    .returns
                    .is_empty()
                    || !abstractor
                        .body(&no, &constants, &result)?
                        .returns
                        .is_empty();
                let continuation = control || (guard && may_return);
                self.continuation_taint |= guard && may_return;
                self.tasks.push(Task::Body(
                    rest,
                    index,
                    env.clone(),
                    continuation,
                    result.clone(),
                ));
                self.tasks.push(Task::Body(
                    if c.boolean()? { yes } else { no },
                    0,
                    env,
                    control || guard,
                    result,
                ));
            }
            Task::Stage(capability, key, ty) => {
                let value = self.pop()?;
                let value = Type::Scalar(ScalarType::parse(&ty)?)
                    .coerce(value)?
                    .value
                    .ok_or_else(|| anyhow!("control stage scalar"))?;
                self.stage(host::Stage {
                    abi_version: 1,
                    operation: host::STAGE.into(),
                    capability,
                    key,
                    ty,
                    value: value.public_json(),
                })?;
            }
        }
        ensure!(
            self.tasks.len() <= 65536 && self.values.len() <= 16384,
            "control continuation limit"
        );
        Ok(())
    }
}

impl Drop for Session {
    fn drop(&mut self) {
        self.clear_writes();
    }
}
