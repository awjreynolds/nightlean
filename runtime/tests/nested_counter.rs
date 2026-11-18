#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Instruction, MODULUS, Plan, check, create_state, field_decimal, prepare, zkir::IrSource,
};
use num_bigint::BigUint;
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str =
    include_str!("fixtures/generic-state/issue69-nested/321/Issue69NestedCounter.bump.impact.json");
const CIRCUIT: &[u8] =
    include_bytes!("fixtures/generic-state/issue69-nested/321/Issue69NestedCounter.bump.zkir");

fn inputs(owner: &[u8; 32], spender: &[u8; 32]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        (
            "owner".into(),
            json!({"kind":"bytes","values":owner.as_slice()}),
        ),
        (
            "spender".into(),
            json!({"kind":"bytes","values":spender.as_slice()}),
        ),
    ])
}

fn assert_epoch(
    state: &ChargedState<Db>,
    owner: &[u8; 32],
    spender: &[u8; 32],
    expected: &str,
    owner_count: usize,
    spender_count: usize,
) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(owners) = array.get(0).unwrap() else {
        panic!("expected owner map")
    };
    assert_eq!(owners.size(), owner_count);
    let owner_key: AlignedValue = (*owner).into();
    let owner = owners.get(&owner_key).expect("owner map exists");
    let StateValue::Map(spenders) = &*owner else {
        panic!("expected nested spender map")
    };
    assert_eq!(spenders.size(), spender_count);
    let spender_key: AlignedValue = (*spender).into();
    let epoch = spenders.get(&spender_key).expect("spender counter exists");
    let StateValue::Cell(epoch) = &*epoch else {
        panic!("expected counter cell")
    };
    let mut fields = Vec::new();
    epoch.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    assert_eq!(field_decimal(fields[0]), expected);
}

#[test]
fn native_nested_maps_preserve_owner_spender_counters_and_guarded_creation() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("epochs".into(), json!([]))])).unwrap();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let zero = [0u8; 32];
    let modulus: [u8; 32] = BigUint::parse_bytes(MODULUS.as_bytes(), 10)
        .unwrap()
        .to_bytes_le()
        .try_into()
        .unwrap();
    let map_constructor = plan
        .operations
        .iter()
        .position(|operation| match operation {
            Instruction::Guarded { operation, .. } => {
                matches!(operation.as_ref(), Instruction::New)
            }
            _ => false,
        })
        .expect("source contains guarded native map creation");

    let first = prepare(
        &plan,
        &inputs(&zero, &modulus),
        &initial,
        parameters,
        address,
    )
    .unwrap();
    assert_eq!(check(&first, &circuit).unwrap(), first.activity_schedule);
    assert_eq!(first.activity_schedule[map_constructor], None);
    assert_epoch(&first.after.state, &zero, &modulus, "1", 1, 1);

    let second = prepare(
        &plan,
        &inputs(&zero, &modulus),
        &first.after.state,
        parameters,
        address,
    )
    .unwrap();
    assert_eq!(check(&second, &circuit).unwrap(), second.activity_schedule);
    assert_eq!(second.activity_schedule[map_constructor], Some(1));
    assert_epoch(&second.after.state, &zero, &modulus, "2", 1, 1);

    let other_owner = prepare(
        &plan,
        &inputs(&modulus, &zero),
        &second.after.state,
        parameters,
        address,
    )
    .unwrap();
    assert_eq!(
        check(&other_owner, &circuit).unwrap(),
        other_owner.activity_schedule
    );
    assert_epoch(&other_owner.after.state, &zero, &modulus, "2", 2, 1);
    assert_epoch(&other_owner.after.state, &modulus, &zero, "1", 2, 1);

    let mut other_spender = prepare(
        &plan,
        &inputs(&zero, &zero),
        &other_owner.after.state,
        parameters,
        address,
    )
    .unwrap();
    assert_eq!(
        check(&other_spender, &circuit).unwrap(),
        other_spender.activity_schedule
    );
    assert_eq!(other_spender.activity_schedule[map_constructor], Some(1));
    assert_epoch(&other_spender.after.state, &zero, &zero, "1", 2, 2);
    assert_epoch(&other_spender.after.state, &zero, &modulus, "2", 2, 2);
    assert_epoch(&other_spender.after.state, &modulus, &zero, "1", 2, 1);

    let mut malformed = plan.clone();
    let path = malformed
        .operations
        .iter_mut()
        .find_map(|operation| match operation {
            Instruction::IndexPath { keys, .. } if !keys.is_empty() => Some(keys),
            _ => None,
        })
        .expect("source reads a nested path");
    path[0].alignment = "field".into();
    assert!(
        prepare(
            &malformed,
            &inputs(&zero, &zero),
            &other_owner.after.state,
            parameters,
            address
        )
        .is_err()
    );

    *other_spender
        .preimage
        .public_transcript_inputs
        .last_mut()
        .unwrap() = Fr::from(9999u64);
    assert!(check(&other_spender, &circuit).is_err());
}
