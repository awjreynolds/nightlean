#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use nightlean_runtime::{
    Db, Instruction, Plan, check, create_state, field_decimal, field_value, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine, Fr};

const NAMES: [&str; 11] = [
    "ownerC1x",
    "ownerC1y",
    "ownerC2x",
    "ownerC2y",
    "spenderC1x",
    "spenderC1y",
    "spenderC2x",
    "spenderC2y",
    "memoX",
    "memoY",
    "memoAmount",
];

fn fields(offset: u64) -> Vec<Fr> {
    let mut fields = Vec::new();
    for index in 1..=5 {
        let point = EmbeddedGroupAffine::generator() * EmbeddedFr::from(offset + index);
        fields.extend([point.x().unwrap(), point.y().unwrap()]);
    }
    fields.push(Fr::from(offset));
    fields
}

fn inputs(owner: &[u8; 32], spender: &[u8; 32], fields: &[Fr]) -> BTreeMap<String, Json> {
    let mut values = BTreeMap::from([
        (
            "owner".into(),
            json!({"kind":"bytes", "values":owner.as_slice()}),
        ),
        (
            "spender".into(),
            json!({"kind":"bytes", "values":spender.as_slice()}),
        ),
    ]);
    values.extend(
        NAMES
            .iter()
            .zip(fields)
            .map(|(name, value)| ((*name).into(), json!(field_decimal(*value)))),
    );
    values
}

fn assert_record(state: &ChargedState<Db>, owner: &[u8; 32], spender: &[u8; 32], fields: &[Fr]) {
    let StateValue::Array(state) = state.get_ref() else {
        panic!("expected root array")
    };
    let StateValue::Map(owners) = state.get(0).unwrap() else {
        panic!("expected owner map")
    };
    let owner_key: AlignedValue = (*owner).into();
    let StateValue::Map(spenders) = &*owners.get(&owner_key).unwrap() else {
        panic!("expected spender map")
    };
    let spender_key: AlignedValue = (*spender).into();
    let StateValue::Cell(record) = &*spenders.get(&spender_key).unwrap() else {
        panic!("expected one record cell")
    };
    let aligned: Vec<_> = fields.iter().map(|value| field_value(*value)).collect();
    assert_eq!(**record, AlignedValue::concat(&aligned));
}

#[test]
fn nested_record_paths_read_write_replace_and_preserve_other_keys() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/nested-escrow/321/NestedEscrow.update.impact.json"
    ))
    .unwrap();
    let circuit: &[u8] = include_bytes!("fixtures/nested-escrow/321/NestedEscrow.update.zkir");
    let circuit = IrSource::load(circuit).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("escrow".into(), json!([]))])).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let first_owner = [0u8; 32];
    let second_owner = [3u8; 32];
    let first_spender = [1u8; 32];
    let second_spender = [2u8; 32];
    let mut state = initial.clone();
    for (owner, spender, offset) in [
        (&first_owner, &first_spender, 10),
        (&first_owner, &second_spender, 20),
        (&second_owner, &first_spender, 30),
        (&first_owner, &first_spender, 40),
    ] {
        let expected = fields(offset);
        let execution = prepare(
            &plan,
            &inputs(owner, spender, &expected),
            &state,
            params,
            address,
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        state = execution.after.state;
        assert_record(&state, owner, spender, &expected);
    }
    assert_record(&state, &first_owner, &first_spender, &fields(40));
    assert_record(&state, &first_owner, &second_spender, &fields(20));
    assert_record(&state, &second_owner, &first_spender, &fields(30));
    let mut malformed = plan.clone();
    malformed
        .operations
        .iter_mut()
        .find_map(|operation| match operation {
            Instruction::PushFields { expressions, .. } => Some(expressions),
            _ => None,
        })
        .unwrap()
        .pop();
    assert!(
        prepare(
            &malformed,
            &inputs(&first_owner, &first_spender, &fields(10)),
            &initial,
            params,
            address
        )
        .is_err()
    );
}
