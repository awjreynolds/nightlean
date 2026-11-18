#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{Db, Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str = include_str!(
    "fixtures/generic-state/issue70-persistent-hash/321/Issue70PersistentHash.register.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "fixtures/generic-state/issue70-persistent-hash/321/Issue70PersistentHash.register.zkir"
);

fn inputs(secret: &[u8; 32], expected: &[u8; 32]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        (
            "secret".into(),
            json!({"kind":"bytes","values":secret.as_slice()}),
        ),
        (
            "expected".into(),
            json!({"kind":"bytes","values":expected.as_slice()}),
        ),
    ])
}

fn assert_registered(state: &ChargedState<Db>, expected: &[u8; 32], count: usize) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(registered) = array.get(0).unwrap() else {
        panic!("expected account map")
    };
    assert_eq!(registered.size(), count);
    let key: AlignedValue = (*expected).into();
    let marker = registered
        .get(&key)
        .expect("exact SHA256 account key exists");
    let StateValue::Cell(marker) = &*marker else {
        panic!("expected registration cell")
    };
    let mut fields = Vec::new();
    marker.value_only_field_repr(&mut fields);
    assert_eq!(fields, vec![Fr::from(1u64)]);
}

#[test]
fn source_persistent_hash_matches_known_account_vectors_and_binds_ledger_keys() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("registered".into(), json!([]))])).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    // Independent SHA256 vectors over the exact 32 raw bytes, without a domain tag.
    let zero = [0u8; 32];
    let zero_id: [u8; 32] =
        hex::decode("66687aadf862bd776c8fc18b8e9f8e20089714856ee233b3902a591d0d5f2925")
            .unwrap()
            .try_into()
            .unwrap();
    let ascending = std::array::from_fn(|index| index as u8);
    let ascending_id: [u8; 32] =
        hex::decode("630dcd2966c4336691125448bbb25b4ff412a49c732db2c8abc1b8581bd710dd")
            .unwrap()
            .try_into()
            .unwrap();

    let first = prepare(&plan, &inputs(&zero, &zero_id), &initial, params, address).unwrap();
    assert_eq!(check(&first, &circuit).unwrap(), first.activity_schedule);
    assert_registered(&first.after.state, &zero_id, 1);

    let repeated = prepare(
        &plan,
        &inputs(&zero, &zero_id),
        &first.after.state,
        params,
        address,
    )
    .unwrap();
    assert_eq!(
        check(&repeated, &circuit).unwrap(),
        repeated.activity_schedule
    );
    assert_registered(&repeated.after.state, &zero_id, 1);

    let mut second = prepare(
        &plan,
        &inputs(&ascending, &ascending_id),
        &repeated.after.state,
        params,
        address,
    )
    .unwrap();
    assert_eq!(check(&second, &circuit).unwrap(), second.activity_schedule);
    assert_registered(&second.after.state, &zero_id, 2);
    assert_registered(&second.after.state, &ascending_id, 2);

    let wrong_expected = prepare(
        &plan,
        &inputs(&zero, &ascending_id),
        &initial,
        params,
        address,
    );
    if let Ok(execution) = wrong_expected {
        assert!(check(&execution, &circuit).is_err());
    }

    // Keep the published key and native transcript fixed while changing the private secret.
    second.preimage.private_transcript[0] = Fr::from(255u64);
    assert!(check(&second, &circuit).is_err());
}
