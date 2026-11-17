//! Lean port of the pinned OpenZeppelin public-supply accounting blocks.
#![cfg(feature = "zkir-321")]

use nightlean_runtime::{Db, Plan, check, create_state, field_decimal, prepare, zkir::IrSource};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::json;
use std::collections::BTreeMap;
use transient_crypto::fab::AlignedValueExt;

const ADD: &str = include_str!(
    "fixtures/openzeppelin-supply/321/OpenZeppelinPort.PublicSupply.addSupply.impact.json"
);
const SUB: &str = include_str!(
    "fixtures/openzeppelin-supply/321/OpenZeppelinPort.PublicSupply.subSupply.impact.json"
);
const ADD_CIRCUIT: &[u8] =
    include_bytes!("fixtures/openzeppelin-supply/321/OpenZeppelinPort.PublicSupply.addSupply.zkir");
const SUB_CIRCUIT: &[u8] =
    include_bytes!("fixtures/openzeppelin-supply/321/OpenZeppelinPort.PublicSupply.subSupply.zkir");

fn total(state: &ChargedState<Db>) -> String {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected contract state")
    };
    let StateValue::Cell(value) = &*array.get(0).unwrap() else {
        panic!("expected supply cell")
    };
    let mut fields = Vec::new();
    value.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

#[test]
fn source_supply_blocks_preserve_128_bit_accounting() {
    let add: Plan = serde_json::from_str(ADD).unwrap();
    let sub: Plan = serde_json::from_str(SUB).unwrap();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let initial = create_state(
        &add,
        &BTreeMap::from([("totalSupply".to_owned(), json!("0"))]),
    )
    .unwrap();
    let minted = prepare(
        &add,
        &BTreeMap::from([("amount".to_owned(), json!("5"))]),
        &initial,
        parameters,
        address,
    )
    .unwrap();
    check(&minted, &IrSource::load(ADD_CIRCUIT).unwrap()).unwrap();
    assert_eq!(total(&minted.after.state), "5");
    let burned = prepare(
        &sub,
        &BTreeMap::from([("amount".to_owned(), json!("2"))]),
        &minted.after.state,
        parameters,
        address,
    )
    .unwrap();
    check(&burned, &IrSource::load(SUB_CIRCUIT).unwrap()).unwrap();
    assert_eq!(total(&burned.after.state), "3");
    assert_eq!(total(&initial), "0");

    let full = create_state(
        &add,
        &BTreeMap::from([(
            "totalSupply".to_owned(),
            json!("340282366920938463463374607431768211455"),
        )]),
    )
    .unwrap();
    let one = BTreeMap::from([("amount".to_owned(), json!("1"))]);
    assert!(prepare(&add, &one, &full, parameters, address).is_err());
    assert!(prepare(&sub, &one, &initial, parameters, address).is_err());
}
