#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Instruction, MODULUS, Plan, check, create_state, field_value, prepare, zkir::IrSource,
};
use num_bigint::BigUint;
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str = include_str!(
    "fixtures/generic-state/issue69-composite/321/Issue69CompositeMap.update.impact.json"
);
const CIRCUIT: &[u8] =
    include_bytes!("fixtures/generic-state/issue69-composite/321/Issue69CompositeMap.update.zkir");

fn inputs(account: &[u8; 32], fields: [u64; 4]) -> BTreeMap<String, Json> {
    let mut inputs = BTreeMap::from([(
        "account".into(),
        json!({"kind":"bytes","values":account.as_slice()}),
    )]);
    for (name, value) in ["c1x", "c1y", "c2x", "c2y"].into_iter().zip(fields) {
        inputs.insert(name.to_owned(), json!(value.to_string()));
    }
    inputs
}

fn assert_record(state: &ChargedState<Db>, account: &[u8; 32], fields: [u64; 4], count: usize) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(balances) = array.get(0).unwrap() else {
        panic!("expected balances map")
    };
    assert_eq!(balances.size(), count);
    let key: AlignedValue = (*account).into();
    let record = balances.get(&key).expect("record exists at exact byte key");
    let StateValue::Cell(record) = &*record else {
        panic!("record must be one native Cell")
    };
    let expected: Vec<_> = fields
        .into_iter()
        .map(|field| field_value(Fr::from(field)))
        .collect();
    assert_eq!(**record, AlignedValue::concat(expected.iter()));
    let mut actual = Vec::new();
    record.value_only_field_repr(&mut actual);
    assert_eq!(actual, fields.into_iter().map(Fr::from).collect::<Vec<_>>());
}

#[test]
fn checked_records_remain_one_aligned_cell_and_bind_each_leaf() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("balances".into(), json!([]))])).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let zero = [0u8; 32];
    let other: [u8; 32] = BigUint::parse_bytes(MODULUS.as_bytes(), 10)
        .unwrap()
        .to_bytes_le()
        .try_into()
        .unwrap();
    let guarded_read = plan
        .operations
        .iter()
        .position(|op| match op {
            Instruction::Guarded { operation, .. } => {
                matches!(operation.as_ref(), Instruction::PopeqFields { .. })
            }
            _ => false,
        })
        .expect("source guards its missing-record lookup");

    let first = prepare(
        &plan,
        &inputs(&zero, [11, 22, 33, 44]),
        &initial,
        params,
        address,
    )
    .unwrap();
    assert_eq!(check(&first, &circuit).unwrap(), first.activity_schedule);
    assert_eq!(first.activity_schedule[guarded_read], Some(10));
    assert_record(&first.after.state, &zero, [11, 22, 33, 44], 1);

    let updated = prepare(
        &plan,
        &inputs(&zero, [101, 202, 303, 404]),
        &first.after.state,
        params,
        address,
    )
    .unwrap();
    assert_eq!(
        check(&updated, &circuit).unwrap(),
        updated.activity_schedule
    );
    assert_eq!(updated.activity_schedule[guarded_read], None);
    assert_record(&updated.after.state, &zero, [101, 202, 303, 404], 1);

    let mut second_key = prepare(
        &plan,
        &inputs(&other, [5, 6, 7, 8]),
        &updated.after.state,
        params,
        address,
    )
    .unwrap();
    assert_eq!(
        check(&second_key, &circuit).unwrap(),
        second_key.activity_schedule
    );
    assert_record(&second_key.after.state, &zero, [101, 202, 303, 404], 2);
    assert_record(&second_key.after.state, &other, [5, 6, 7, 8], 2);

    let mut malformed = plan.clone();
    let fields = malformed
        .operations
        .iter_mut()
        .find_map(|op| match op {
            Instruction::PushFields { expressions, .. } => Some(expressions),
            _ => None,
        })
        .unwrap();
    fields.pop();
    assert!(
        prepare(
            &malformed,
            &inputs(&zero, [11, 22, 33, 44]),
            &initial,
            params,
            address
        )
        .is_err()
    );

    *second_key
        .preimage
        .public_transcript_outputs
        .last_mut()
        .unwrap() = Fr::from(9999u64);
    assert!(check(&second_key, &circuit).is_err());
}
