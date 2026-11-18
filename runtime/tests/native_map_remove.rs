#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{Db, Plan, check, field_value, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use storage::{arena::Sp, storage::HashMap};
use transient_crypto::curve::Fr;

fn state(include_target: bool) -> ChargedState<Db> {
    let record = |x: u64| {
        StateValue::Cell(Sp::new(AlignedValue::concat(&[
            field_value(Fr::from(x)),
            field_value(Fr::from(x + 1)),
        ])))
    };
    let mut first_owner = HashMap::new().insert([2u8; 32].into(), record(20));
    if include_target {
        first_owner = first_owner.insert([1u8; 32].into(), record(10));
    }
    let owners = HashMap::new()
        .insert([0u8; 32].into(), StateValue::Map(first_owner))
        .insert(
            [3u8; 32].into(),
            StateValue::Map(HashMap::new().insert([1u8; 32].into(), record(30))),
        );
    ChargedState::new(StateValue::Array(vec![StateValue::Map(owners)].into()))
}

fn inputs(owner: u8, enabled: bool) -> BTreeMap<String, Json> {
    BTreeMap::from([
        (
            "owner".into(),
            json!({"kind":"bytes", "values":vec![owner;32]}),
        ),
        (
            "spender".into(),
            json!({"kind":"bytes", "values":vec![1u8;32]}),
        ),
        ("enabled".into(), json!(enabled)),
    ])
}

#[test]
fn map_remove_preserves_siblings_and_matches_native_missing_key_behavior() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/native-map-remove/321/NativeMapRemove.remove.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/native-map-remove/321/NativeMapRemove.remove.zkir").as_slice(),
    )
    .unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let initial = state(true);
    let removed = prepare(&plan, &inputs(0, true), &initial, params, address).unwrap();
    check(&removed, &circuit).unwrap();
    assert_eq!(removed.after.state, state(false));

    // Removing an absent leaf is idempotent, while an absent parent is an invalid path.
    let repeated = prepare(
        &plan,
        &inputs(0, true),
        &removed.after.state,
        params,
        address,
    )
    .unwrap();
    check(&repeated, &circuit).unwrap();
    assert_eq!(repeated.after.state, removed.after.state);
    assert!(prepare(&plan, &inputs(9, true), &initial, params, address).is_err());

    let inactive = prepare(&plan, &inputs(9, false), &initial, params, address).unwrap();
    check(&inactive, &circuit).unwrap();
    assert_eq!(inactive.after.state, initial);
}
