#![cfg(feature = "zkir-321")]

use nightlean_runtime::{
    Db, Expr, Instruction, Plan, check, create_state, field_decimal, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;
use transient_crypto::fab::AlignedValueExt;

const PLAN: &str = include_str!(
    "fixtures/generic-state/issue43-effect-blocks/321/Issue43EffectBlocks.update.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "fixtures/generic-state/issue43-effect-blocks/321/Issue43EffectBlocks.update.zkir"
);

fn plan() -> Plan {
    serde_json::from_str(PLAN).expect("source-generated effect-block plan parses")
}

fn state(plan: &Plan) -> ChargedState<Db> {
    create_state(
        plan,
        &BTreeMap::from([
            ("left".to_owned(), json!("11")),
            ("right".to_owned(), json!("22")),
            ("selected".to_owned(), json!("0")),
            ("nested".to_owned(), json!("0")),
            ("final".to_owned(), json!("0")),
        ]),
    )
    .expect("source state creates native ledger state")
}

fn cell(state: &ChargedState<Db>, slot: usize) -> String {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Cell(cell) = &*array.get(slot).expect("cell slot exists") else {
        panic!("expected state cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

fn inputs(choose: bool, wide: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("choose".to_owned(), json!(choose)),
        ("wide".to_owned(), json!(wide.to_string())),
    ])
}

fn execute(
    plan: &Plan,
    choose: bool,
    wide: u64,
    initial: &ChargedState<Db>,
) -> nightlean_runtime::Execution {
    prepare(
        plan,
        &inputs(choose, wide),
        initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .expect("source effects materialize against native state")
}

#[test]
fn nested_effect_blocks_bind_branch_locals_and_preserve_order() {
    let plan = plan();
    let initial = state(&plan);
    let circuit = IrSource::load(CIRCUIT).expect("source ZKIR parses");

    let then_branch = execute(&plan, true, 3, &initial);
    assert_eq!(cell(&then_branch.after.state, 2), "11");
    assert_eq!(cell(&then_branch.after.state, 3), "31");
    assert_eq!(cell(&then_branch.after.state, 4), "11");
    assert_eq!(
        check(&then_branch, &circuit).unwrap(),
        then_branch.activity_schedule
    );

    let nested_else = execute(&plan, true, 2, &initial);
    assert_eq!(cell(&nested_else.after.state, 2), "11");
    assert_eq!(cell(&nested_else.after.state, 3), "32");
    assert_eq!(cell(&nested_else.after.state, 4), "11");
    assert!(check(&nested_else, &circuit).is_ok());

    // The nested narrowing cast is out of range. Its parent branch is inactive,
    // so preparation skips it and the selected else arm still runs.
    let else_branch = execute(&plan, false, 8, &initial);
    assert_eq!(cell(&else_branch.after.state, 2), "22");
    assert_eq!(cell(&else_branch.after.state, 3), "42");
    assert_eq!(cell(&else_branch.after.state, 4), "22");
    assert_eq!(
        check(&else_branch, &circuit).unwrap(),
        else_branch.activity_schedule
    );

    assert!(
        prepare(
            &plan,
            &inputs(true, 8),
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .is_err()
    );

    let mut altered_guard = plan.clone();
    let Some(Instruction::Guarded { guard, .. }) = altered_guard
        .operations
        .iter_mut()
        .find(|operation| matches!(operation, Instruction::Guarded { .. }))
    else {
        panic!("branch Impact operation is guarded")
    };
    *guard = Expr::Bool { value: false };
    let mismatched = prepare(
        &altered_guard,
        &inputs(true, 3),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    );
    if let Ok(mismatched) = mismatched {
        assert!(check(&mismatched, &circuit).is_err());
    }

    let mut altered_transcript = execute(&plan, true, 3, &initial);
    let last = altered_transcript
        .preimage
        .public_transcript_inputs
        .last_mut()
        .expect("active branch reads bind transcript fields");
    *last = Fr::from(9999u64);
    assert!(check(&altered_transcript, &circuit).is_err());
}
