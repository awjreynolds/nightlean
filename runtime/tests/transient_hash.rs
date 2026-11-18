#![cfg(feature = "zkir-321")]

use noctium_runtime::{Expr, Plan, check, create_state, field_decimal, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, hash::transient_hash};

const PLAN: &str = include_str!("fixtures/transient-hash/321/TransientHash.hash.impact.json");
const CIRCUIT: &[u8] = include_bytes!("fixtures/transient-hash/321/TransientHash.hash.zkir");

fn inputs(values: &[u64; 5], enabled: bool) -> BTreeMap<String, Json> {
    let mut supplied: BTreeMap<_, _> = ["a", "b", "c", "d", "e"]
        .into_iter()
        .zip(values)
        .map(|(name, value)| (name.into(), json!(value.to_string())))
        .collect();
    supplied.insert("enabled".into(), json!(enabled));
    supplied
}

fn digest(values: &[u64]) -> Json {
    json!(field_decimal(transient_hash(
        &values.iter().copied().map(Fr::from).collect::<Vec<_>>()
    )))
}

#[test]
fn transient_hash_binds_order_length_legacy_form_and_cached_operand_assertions() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let values = [1, 2, 3, 4, 5];
    let supplied = inputs(&values, true);
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let mut execution = prepare(&plan, &supplied, &initial, params, address).unwrap();
    assert_eq!(
        check(&execution, &circuit).unwrap(),
        execution.activity_schedule
    );
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("empty".into(), json!("0")),
            ("single".into(), digest(&[1])),
            ("legacy".into(), digest(&[7, 1, 2])),
            ("triple".into(), digest(&[7, 1, 2])),
            ("ordered".into(), digest(&values)),
            ("checked".into(), digest(&values)),
        ])
    );
    assert_eq!(execution.after.state, initial);
    assert_eq!(execution.preimage.private_transcript.len(), 6);
    assert_ne!(digest(&values), digest(&[2, 1, 3, 4, 5]));
    assert_ne!(digest(&values), digest(&[1, 2, 3, 4]));
    assert_ne!(digest(&[1]), digest(&[1, 0]));
    assert!(prepare(&plan, &inputs(&values, false), &initial, params, address).is_err());
    execution.preimage.private_transcript[5] = Fr::from(0u64);
    assert!(check(&execution, &circuit).is_err());
    execution.preimage.private_transcript[5] = Fr::from(1u64);
    execution.preimage.private_transcript[0] = Fr::from(9u64);
    assert!(check(&execution, &circuit).is_err());

    let mut changed_order = plan.clone();
    let value = &mut changed_order
        .circuit
        .outputs
        .iter_mut()
        .find(|output| output.name == "orderedHash")
        .unwrap()
        .expression;
    let Expr::TransientHash { values } = value else {
        panic!("expected transient hash")
    };
    values.swap(0, 1);
    let changed = prepare(&changed_order, &supplied, &initial, params, address).unwrap();
    assert!(check(&changed, &circuit).is_err());
    let mut changed_return = plan.clone();
    changed_return.returns[4].expression = Expr::Constant { value: "0".into() };
    let changed = prepare(&changed_return, &supplied, &initial, params, address).unwrap();
    assert!(check(&changed, &circuit).is_err());
}
