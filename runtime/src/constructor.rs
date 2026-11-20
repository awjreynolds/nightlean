//! Public constructor evaluation and immutable deployment cells.
use crate::{Db, Expr, Plan, ScalarType, StateDecl, create_state, evaluate, input_value};
use anyhow::{Result, anyhow, bail, ensure};
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use onchain_runtime::state::{ChargedState, StateValue};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::collections::{BTreeMap, BTreeSet};

const MAX_CONSTRUCTOR_BYTES: usize = 1_048_576;

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Constructor {
    pub parameters: Vec<Parameter>,
    pub initializers: Vec<Initializer>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Parameter {
    pub name: String,
    #[serde(rename = "type")]
    pub ty: String,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Initializer {
    pub state: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub value: InitialValue,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
pub enum InitialValue {
    ScalarExpression { expression: Expr },
    OpaqueStringParameter { name: String },
    OpaqueStringLiteral { value: String },
}

pub(crate) fn opaque_string(value: &Json) -> Result<AlignedValue> {
    let text = value
        .as_str()
        .ok_or_else(|| anyhow!("expected opaque UTF-8 string"))?;
    ensure!(
        text.len() <= MAX_CONSTRUCTOR_BYTES,
        "opaque string exceeds byte limit"
    );
    // ValueAtom::from trims trailing zero bytes, which changes a string ending in U+0000.
    AlignedValue::new(
        FabValue(vec![ValueAtom(text.as_bytes().to_vec())]),
        Alignment::singleton(AlignmentAtom::Compress),
    )
    .ok_or_else(|| anyhow!("invalid opaque string alignment"))
}

/// Decode the declared UTF-8 metadata representation without trimming zero bytes.
pub fn decode_opaque_string(value: &AlignedValue) -> Result<String> {
    ensure!(
        value.alignment == Alignment::singleton(AlignmentAtom::Compress)
            && value.value.0.len() == 1,
        "invalid opaque string alignment"
    );
    let bytes = &value.value.0[0].0;
    ensure!(
        bytes.len() <= MAX_CONSTRUCTOR_BYTES,
        "opaque string exceeds byte limit"
    );
    Ok(String::from_utf8(bytes.clone())?)
}

fn cell_type(decl: &StateDecl) -> Result<&str> {
    if decl.kind.get("opaqueString") == Some(&Json::Bool(true)) {
        Ok("OpaqueString")
    } else {
        decl.kind
            .get("cell")
            .and_then(Json::as_str)
            .ok_or_else(|| anyhow!("constructor initializer must select a cell"))
    }
}

fn scalar_zero(ty: &str) -> Result<Json> {
    Ok(match ScalarType::parse(ty)? {
        ScalarType::Native | ScalarType::UInt(_) => json!("0"),
        ScalarType::Bool => json!(false),
        ScalarType::Bytes32 => json!({"kind":"bytes", "values":vec![0u8;32]}),
        ScalarType::Bytes(length) => json!({"kind":"bytes", "values":vec![0u8;length]}),
        ScalarType::JubjubScalar => json!({"kind":"jubjubScalar", "value":"0"}),
        ScalarType::JubjubPoint => json!({"kind":"jubjubPoint", "x":"0", "y":"1"}),
        #[cfg(feature = "zkir-321")]
        ScalarType::Foreign(ty) => {
            let value = crate::foreign::ForeignValue::zero(ty)?;
            json!({"kind":"foreign", "type":ty.source_name(), "bytes":value.to_bytes()?})
        }
    })
}

fn default_value(decl: &StateDecl) -> Result<Json> {
    if decl.kind.get("opaqueString") == Some(&Json::Bool(true)) {
        return Ok(json!(""));
    }
    if let Some(ty) = decl.kind.get("cell").and_then(Json::as_str) {
        return scalar_zero(ty);
    }
    if let Some(schema) = decl.kind.get("tree") {
        if schema.get("counter") == Some(&Json::Bool(true)) {
            return Ok(json!("0"));
        }
        if schema.get("set").is_some() {
            return Ok(json!([]));
        }
        if let Some(ty) = schema.get("scalar").and_then(Json::as_str) {
            return scalar_zero(ty);
        }
        if let Some(record) = schema.get("composite") {
            let checked = crate::checked_record_schema(record)?;
            return Ok(serde_json::from_slice(
                &checked.from_leaf_json(&vec![json!("0"); checked.counts().leaves])?,
            )?);
        }
    }
    // create_state validates collection schemas and requires these defaults to be empty.
    Ok(json!([]))
}

/// Build fresh genesis from the artifact's public constructor arguments.
/// This evaluates source initialization off chain; the ledger has no constructor proof.
pub fn construct_state(
    plan: &Plan,
    arguments: &BTreeMap<String, Json>,
) -> Result<ChargedState<Db>> {
    let constructor = plan
        .constructor
        .as_ref()
        .ok_or_else(|| anyhow!("artifact has no constructor"))?;
    ensure!(plan.state.len() <= 16, "state array exceeds native limit");
    ensure!(
        constructor.parameters.len() <= 64,
        "too many constructor parameters"
    );
    ensure!(
        constructor.initializers.len() <= plan.state.len(),
        "too many constructor initializers"
    );
    let mut expected = BTreeSet::new();
    let mut scalars = BTreeMap::new();
    let mut strings = BTreeMap::new();
    let mut string_bytes = 0usize;
    for parameter in &constructor.parameters {
        ensure!(
            !parameter.name.is_empty() && expected.insert(parameter.name.as_str()),
            "invalid or duplicate constructor parameter"
        );
        let value = arguments
            .get(&parameter.name)
            .ok_or_else(|| anyhow!("missing constructor argument"))?;
        if parameter.ty == "OpaqueString" {
            let text = value
                .as_str()
                .ok_or_else(|| anyhow!("expected opaque UTF-8 string"))?;
            string_bytes = string_bytes
                .checked_add(text.len())
                .ok_or_else(|| anyhow!("constructor byte size overflow"))?;
            ensure!(
                string_bytes <= MAX_CONSTRUCTOR_BYTES,
                "constructor string byte limit"
            );
            strings.insert(parameter.name.as_str(), value);
        } else {
            scalars.insert(parameter.name.clone(), input_value(&parameter.ty, value)?);
        }
    }
    ensure!(
        arguments.len() == expected.len()
            && arguments
                .keys()
                .all(|name| expected.contains(name.as_str())),
        "constructor argument schema mismatch"
    );
    let mut config = BTreeMap::new();
    for declaration in &plan.state {
        ensure!(
            !declaration.name.is_empty() && !config.contains_key(&declaration.name),
            "invalid or duplicate state name"
        );
        config.insert(declaration.name.clone(), default_value(declaration)?);
    }
    let mut initialized = BTreeSet::new();
    for initializer in &constructor.initializers {
        ensure!(
            initialized.insert(initializer.state.as_str()),
            "duplicate constructor initializer"
        );
        let declaration = plan
            .state
            .iter()
            .find(|decl| decl.name == initializer.state)
            .ok_or_else(|| anyhow!("unknown constructor state cell"))?;
        ensure!(
            cell_type(declaration)? == initializer.ty,
            "constructor initializer type mismatch"
        );
        let value = match &initializer.value {
            InitialValue::ScalarExpression { expression } => {
                ensure!(
                    initializer.ty != "OpaqueString",
                    "opaque string requires typed initializer"
                );
                let value = evaluate(expression, &scalars)?;
                ensure!(
                    value.scalar_type() == ScalarType::parse(&initializer.ty)?,
                    "constructor scalar expression type mismatch"
                );
                value.validate()?;
                value.public_json()
            }
            InitialValue::OpaqueStringParameter { name } => {
                ensure!(
                    initializer.ty == "OpaqueString",
                    "string initializer type mismatch"
                );
                (*strings
                    .get(name.as_str())
                    .ok_or_else(|| anyhow!("unknown opaque string parameter"))?)
                .clone()
            }
            InitialValue::OpaqueStringLiteral { value } => {
                ensure!(
                    initializer.ty == "OpaqueString",
                    "string initializer type mismatch"
                );
                json!(value)
            }
        };
        config.insert(initializer.state.clone(), value);
    }
    for declaration in &plan.state {
        if declaration.sealed {
            cell_type(declaration)?;
            ensure!(
                initialized.contains(declaration.name.as_str()),
                "sealed cell lacks constructor initialization"
            );
        }
    }
    create_state(plan, &config)
}

pub(crate) fn deployment_state(
    plan: &Plan,
    config: &BTreeMap<String, Json>,
) -> Result<ChargedState<Db>> {
    if plan.constructor.is_some() {
        construct_state(plan, config)
    } else {
        create_state(plan, config)
    }
}

pub(crate) fn check_sealed_state(
    plan: &Plan,
    before: &ChargedState<Db>,
    after: &ChargedState<Db>,
) -> Result<()> {
    if !plan.state.iter().any(|decl| decl.sealed) {
        return Ok(());
    }
    let (StateValue::Array(before), StateValue::Array(after)) = (before.get_ref(), after.get_ref())
    else {
        bail!("sealed state requires array storage")
    };
    for (slot, declaration) in plan.state.iter().enumerate() {
        if declaration.sealed {
            ensure!(
                before.get(slot).is_some() && before.get(slot) == after.get(slot),
                "entrypoint changed sealed state cell"
            );
        }
    }
    Ok(())
}
