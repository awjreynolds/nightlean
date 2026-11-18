#![cfg(feature = "zkir-321")]

use noctium_runtime::{Db, Plan, check, create_state, field_decimal, prepare, zkir::IrSource};
use onchain_runtime::ops::Op;
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str =
    include_str!("fixtures/native-helper-branches/321/NativeHelperBranches.update.impact.json");
const CIRCUIT: &[u8] =
    include_bytes!("fixtures/native-helper-branches/321/NativeHelperBranches.update.zkir");

fn inputs(enabled: bool, value: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("enabled".into(), json!(enabled)),
        ("value".into(), json!(value.to_string())),
    ])
}

fn balance(state: &ChargedState<Db>) -> String {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let StateValue::Cell(cell) = &*array.get(0).expect("balance cell exists") else {
        panic!("expected balance cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

#[test]
fn helper_branch_restores_outer_binding_and_guards_partial_evaluation() {
    let plan: Plan = serde_json::from_str(PLAN).expect("source-generated helper plan parses");
    let circuit = IrSource::load(CIRCUIT).expect("source ZKIR parses");
    let initial = create_state(&plan, &BTreeMap::from([("balance".into(), json!("3"))]))
        .expect("initial balance state parses");
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    let active = prepare(&plan, &inputs(true, 7), &initial, params, address)
        .expect("active helper assertion and narrowing succeed");
    check(&active, &circuit).expect("active helper relation checks");
    assert_eq!(balance(&active.after.state), "7");
    assert_eq!(
        active.returns_json(),
        BTreeMap::from([("observed".into(), json!("7"))])
    );

    let mut inactive = prepare(&plan, &inputs(false, 8), &initial, params, address)
        .expect("inactive helper branch skips assertion and narrowing");
    assert_eq!(inactive.program.len(), 2);
    assert!(matches!(
        inactive.program[0],
        Op::Push { storage: false, .. }
    ));
    assert!(matches!(inactive.program[1], Op::Popeq { .. }));
    assert_eq!(inactive.preimage.private_transcript.len(), 1);
    check(&inactive, &circuit).expect("inactive helper relation checks");
    assert_eq!(inactive.after.state, initial);
    assert_eq!(balance(&inactive.after.state), "3");
    assert_eq!(
        inactive.returns_json(),
        BTreeMap::from([("observed".into(), json!("8"))])
    );

    assert!(prepare(&plan, &inputs(true, 8), &initial, params, address).is_err());

    inactive.preimage.private_transcript[0] = Fr::from(1u64);
    assert!(check(&inactive, &circuit).is_err());
}
