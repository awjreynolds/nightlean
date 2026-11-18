#![cfg(feature = "zkir-321")]

use noctium_runtime::{
    Db, Expr, Instruction, Plan, check, create_state, field_decimal, field_value, prepare,
    zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str = include_str!(
    "fixtures/generic-state/issue43-membership/321/Issue43MapMembership.initOnce.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "fixtures/generic-state/issue43-membership/321/Issue43MapMembership.initOnce.zkir"
);

fn plan() -> Plan {
    serde_json::from_str(PLAN).expect("source-generated membership plan parses")
}

fn empty_state(plan: &Plan) -> ChargedState<Db> {
    create_state(plan, &BTreeMap::from([("balances".to_owned(), json!([]))]))
        .expect("source map creates native ledger state")
}

fn inputs(account: u64, proposed: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("account".to_owned(), json!(account.to_string())),
        ("proposed".to_owned(), json!(proposed.to_string())),
    ])
}

fn balance(state: &ChargedState<Db>, account: u64) -> Option<String> {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(map) = &*array.get(0).expect("map slot exists") else {
        panic!("expected state map")
    };
    let value = map.get(&field_value(Fr::from(account)))?;
    let StateValue::Cell(cell) = &*value else {
        panic!("expected map value cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    Some(field_decimal(fields[0]))
}

fn operation_fields(instruction: &Instruction) -> usize {
    match instruction {
        Instruction::Guarded { operation, .. } => operation_fields(operation),
        Instruction::Dup | Instruction::Member | Instruction::Insert { .. } | Instruction::New => 1,
        Instruction::Index { key: None, .. } => 4,
        Instruction::Index { key: Some(_), .. } => 7,
        Instruction::Push { .. } => 5,
        Instruction::Popeq { .. } => 4,
        Instruction::IndexPath { .. } => panic!("this scalar fixture has no path operations"),
        Instruction::PushFields { .. } | Instruction::PopeqFields { .. } => {
            panic!("this scalar fixture has no grouped record operations")
        }
    }
}

fn member_result_index(plan: &Plan) -> usize {
    let mut offset = 0;
    for instruction in &plan.operations {
        if matches!(
            instruction,
            Instruction::Popeq {
                expression: Expr::Reference { name },
                alignment,
            } if name == "present" && alignment == "bit"
        ) {
            return offset + 3;
        }
        offset += operation_fields(instruction);
    }
    panic!("membership Bool read exists in source plan")
}

#[test]
fn membership_read_initializes_only_absent_map_keys_and_binds_native_result() {
    let plan = plan();
    let circuit = IrSource::load(CIRCUIT).expect("source ZKIR parses");
    let initial = empty_state(&plan);
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    let first = prepare(&plan, &inputs(7, 13), &initial, params, address)
        .expect("absent membership query passes native state preparation");
    assert_eq!(balance(&first.after.state, 7).as_deref(), Some("13"));
    assert!(check(&first, &circuit).is_ok());
    assert!(first.activity_schedule[13..].iter().all(Option::is_none));

    let present_after_write = prepare(&plan, &inputs(8, 77), &initial, params, address)
        .expect("membership query sees the earlier ordered write");
    assert_eq!(
        balance(&present_after_write.after.state, 8).as_deref(),
        Some("99")
    );
    assert_eq!(
        &present_after_write.activity_schedule[13..],
        [Some(4), Some(5), Some(5), Some(1)]
    );
    assert!(check(&present_after_write, &circuit).is_ok());

    let second = prepare(&plan, &inputs(7, 17), &first.after.state, params, address)
        .expect("present membership query passes native state preparation");
    assert_eq!(balance(&second.after.state, 7).as_deref(), Some("13"));
    assert_eq!(
        &second.activity_schedule[13..],
        [Some(4), Some(5), Some(5), Some(1)]
    );
    assert!(check(&second, &circuit).is_ok());

    let mut forged_membership = first;
    let index = member_result_index(&plan);
    forged_membership.preimage.public_transcript_inputs[index] = Fr::from(1u64);
    assert!(check(&forged_membership, &circuit).is_err());
}
