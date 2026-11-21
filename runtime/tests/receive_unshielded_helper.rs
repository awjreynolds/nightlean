#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::{
    coin::{TokenType, UnshieldedTokenType},
    contract::ContractAddress,
};
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::context::QueryContext;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_RECEIVE_UNSHIELDED_DIR")
        .map(PathBuf::from)
        .expect("set fresh ReceiveUnshielded outputs in NOCTIUM_RECEIVE_UNSHIELDED_DIR")
}

fn inputs(color: &[u8; 32], enabled: bool) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("color".into(), json!({"kind":"bytes", "values":color})),
        ("amount".into(), json!("7")),
        ("enabled".into(), json!(enabled)),
    ])
}

fn expected_input(
    plan: &Plan,
    circuit: &IrSource,
    color: HashOutput,
    enabled: bool,
) -> anyhow::Result<Option<u128>> {
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let state = create_state(plan, &BTreeMap::new())?;
    let context = QueryContext::new(state, ContractAddress::default());
    let execution =
        prepare_with_context(plan, &inputs(&color.0, enabled), context.clone(), params)?;
    assert_eq!(check(&execution, circuit)?, execution.activity_schedule);
    let effects = context
        .query(
            &execution.program,
            None,
            &params.cost_model.runtime_cost_model,
        )?
        .context
        .effects;
    let token = TokenType::Unshielded(UnshieldedTokenType(color));
    assert_eq!(
        effects.unshielded_inputs.iter().count(),
        usize::from(enabled)
    );
    assert_eq!(effects.unshielded_outputs.iter().count(), 0);
    assert_eq!(effects.claimed_unshielded_spends.iter().count(), 0);
    Ok(effects.unshielded_inputs.get(&token).map(|amount| *amount))
}

#[test]
#[ignore = "requires fresh Lean artifacts in NOCTIUM_RECEIVE_UNSHIELDED_DIR"]
fn helper_matches_explicit_unshielded_input_plan_and_runtime() -> anyhow::Result<()> {
    let directory = artifacts();
    let helper_json: Json = serde_json::from_slice(&fs::read(
        directory.join("ReceiveUnshielded.receive.impact.json"),
    )?)?;
    let primitive_json: Json = serde_json::from_slice(&fs::read(
        directory.join("ReceiveUnshielded.primitive.impact.json"),
    )?)?;
    assert_eq!(helper_json["circuit"], primitive_json["circuit"]);
    assert_eq!(helper_json["operations"], primitive_json["operations"]);
    assert_eq!(helper_json["guards"], primitive_json["guards"]);
    assert_eq!(helper_json["reads"], primitive_json["reads"]);

    let helper: Plan = serde_json::from_value(helper_json)?;
    let primitive: Plan = serde_json::from_value(primitive_json)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("ReceiveUnshielded.receive.zkir"),
    )?)?;
    let color = HashOutput(std::array::from_fn(|index| (index + 1) as u8));
    for enabled in [true, false] {
        let expected = enabled.then_some(7);
        assert_eq!(expected_input(&helper, &circuit, color, enabled)?, expected);
        assert_eq!(
            expected_input(&primitive, &circuit, color, enabled)?,
            expected
        );
    }
    Ok(())
}
