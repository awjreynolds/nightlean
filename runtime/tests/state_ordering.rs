use noctium_runtime::{
    Db, Execution, Expr, Plan, Value, canonical_field, check, create_state, evaluate,
    field_decimal, field_value, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::json;
use std::collections::BTreeMap;
use storage::arena::Sp;
use transient_crypto::fab::AlignedValueExt;

#[cfg(feature = "zkir-320")]
const SEQUENTIAL_PLAN: &str =
    include_str!("fixtures/issue65/OrderedState.sequential-320.impact.json");
#[cfg(feature = "zkir-321")]
const SEQUENTIAL_PLAN: &str =
    include_str!("fixtures/issue65/OrderedState.sequential-321.impact.json");
const SEQUENTIAL_CIRCUIT: &[u8] = include_bytes!("fixtures/issue65/OrderedState.sequential.zkir");
#[cfg(feature = "zkir-320")]
const FAILING_GUARD_PLAN: &str =
    include_str!("fixtures/issue65/OrderedState.failingGuard-320.impact.json");
#[cfg(feature = "zkir-321")]
const FAILING_GUARD_PLAN: &str =
    include_str!("fixtures/issue65/OrderedState.failingGuard-321.impact.json");
const FAILING_GUARD_CIRCUIT: &[u8] =
    include_bytes!("fixtures/issue65/OrderedState.failingGuard.zkir");
#[cfg(feature = "zkir-320")]
const NONCANONICAL_PLAN: &str =
    include_str!("fixtures/issue65/OrderedState.noncanonicalRead-320.impact.json");
#[cfg(feature = "zkir-321")]
const NONCANONICAL_PLAN: &str =
    include_str!("fixtures/issue65/OrderedState.noncanonicalRead-321.impact.json");
#[cfg(feature = "zkir-320")]
const PRIVATE_CLAIM_PLAN: &str =
    include_str!("fixtures/issue65/PrivateClaim.claim-320.impact.json");
#[cfg(feature = "zkir-321")]
const PRIVATE_CLAIM_PLAN: &str =
    include_str!("fixtures/issue65/PrivateClaim.claim-321.impact.json");
const PRIVATE_CLAIM_CIRCUIT: &[u8] = include_bytes!("fixtures/issue65/PrivateClaim.claim.zkir");

fn state(plan: &Plan) -> ChargedState<Db> {
    create_state(
        plan,
        &serde_json::from_value(json!({
            "counter":"0",
            "untouched":"9",
            "flag":false,
            "amount":"0",
            "spent":[]
        }))
        .unwrap(),
    )
    .unwrap()
}

fn selected_plan(raw: &str) -> Plan {
    serde_json::from_str(raw).unwrap()
}

fn cell_decimal(state: &ChargedState<Db>, slot: usize) -> String {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected root state array")
    };
    let cell = array.get(slot).expect("expected declared state slot");
    let StateValue::Cell(value) = &*cell else {
        panic!("expected state cell")
    };
    let mut fields = Vec::new();
    value.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

fn map_len(state: &ChargedState<Db>, slot: usize) -> usize {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected root state array")
    };
    let map = array.get(slot).expect("expected declared state slot");
    let StateValue::Map(map) = &*map else {
        panic!("expected state map")
    };
    map.size()
}

fn prepare_plan(plan: &Plan, state: &ChargedState<Db>) -> Execution {
    prepare(
        plan,
        &BTreeMap::new(),
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap()
}

fn poseidon2(domain: &str, left: &str, right: &str) -> String {
    let expression: Expr = serde_json::from_value(json!({
        "tag":"poseidon2",
        "domain":domain,
        "left":{"tag":"constant","value":left},
        "right":{"tag":"constant","value":right}
    }))
    .unwrap();
    let Value::Native(value) = evaluate(&expression, &BTreeMap::new()).unwrap() else {
        panic!("Poseidon2 returned a non-Native value")
    };
    field_decimal(value)
}

#[test]
fn emitted_source_ordering_matches_native_state_and_transcript() {
    let plan = selected_plan(SEQUENTIAL_PLAN);
    let initial = state(&plan);
    let before = initial.clone();
    let execution = prepare_plan(&plan, &initial);
    let circuit = IrSource::load(SEQUENTIAL_CIRCUIT).unwrap();

    assert_eq!(
        check(&execution, &circuit).unwrap().len(),
        execution.program.len()
    );
    assert_eq!(
        execution
            .preimage
            .public_transcript_outputs
            .iter()
            .copied()
            .map(field_decimal)
            .collect::<Vec<_>>(),
        ["0", "1", "2", "9", "1", "255", "9"]
    );
    assert_eq!(cell_decimal(&execution.after.state, 0), "2");
    assert_eq!(cell_decimal(&execution.after.state, 1), "9");
    assert_eq!(cell_decimal(&execution.after.state, 2), "1");
    assert_eq!(cell_decimal(&execution.after.state, 3), "255");
    assert_eq!(map_len(&execution.after.state, 4), 1);
    assert_eq!(initial, before);
}

#[test]
fn private_claim_keeps_prewrite_read_and_preimage_behavior() {
    let plan: Plan = serde_json::from_str(PRIVATE_CLAIM_PLAN).unwrap();
    let campaign = "5";
    let leaf = poseidon2("1", "3", campaign);
    let node = poseidon2("2", &leaf, "7");
    let root = poseidon2("2", &node, "11");
    let nullifier = poseidon2("3", "3", campaign);
    let inputs = BTreeMap::from([
        ("root".into(), json!(root.clone())),
        ("campaign".into(), json!(campaign)),
        ("suppliedNullifier".into(), json!(nullifier.clone())),
        ("secret".into(), json!("3")),
        ("sibling0".into(), json!("7")),
        ("sibling1".into(), json!("11")),
        ("direction0".into(), json!(false)),
        ("direction1".into(), json!(false)),
    ]);
    let initial = create_state(
        &plan,
        &serde_json::from_value(json!({
            "acceptedRoot":root.clone(),
            "campaignId":campaign,
            "spent":[]
        }))
        .unwrap(),
    )
    .unwrap();
    let before = initial.clone();
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    let circuit = IrSource::load(PRIVATE_CLAIM_CIRCUIT).unwrap();

    assert_eq!(
        check(&execution, &circuit).unwrap().len(),
        execution.program.len()
    );
    assert_eq!(
        execution
            .preimage
            .public_transcript_outputs
            .iter()
            .copied()
            .map(field_decimal)
            .collect::<Vec<_>>(),
        [
            root.as_str(),
            campaign,
            nullifier.as_str(),
            root.as_str(),
            campaign,
            "0"
        ]
    );
    assert_eq!(
        execution
            .preimage
            .private_transcript
            .iter()
            .copied()
            .map(field_decimal)
            .collect::<Vec<_>>(),
        ["3", "7", "11", "0", "0"]
    );
    assert_eq!(cell_decimal(&execution.after.state, 0), root);
    assert_eq!(cell_decimal(&execution.after.state, 1), campaign);
    assert_eq!(map_len(&execution.after.state, 2), 1);
    assert_eq!(initial, before);
}

#[test]
fn inconsistent_read_values_fail_native_check_without_mutating_input_state() {
    let plan = selected_plan(SEQUENTIAL_PLAN);
    let initial = state(&plan);
    let before = initial.clone();
    let mut execution = prepare_plan(&plan, &initial);
    execution.preimage.public_transcript_outputs[1] = canonical_field("7").unwrap();
    let circuit = IrSource::load(SEQUENTIAL_CIRCUIT).unwrap();

    assert!(check(&execution, &circuit).is_err());
    assert_eq!(initial, before);
}

#[test]
fn failed_source_guard_fails_native_check_without_mutating_input_state() {
    let plan = selected_plan(FAILING_GUARD_PLAN);
    let initial = state(&plan);
    let before = initial.clone();
    let execution = prepare_plan(&plan, &initial);
    let circuit = IrSource::load(FAILING_GUARD_CIRCUIT).unwrap();

    assert!(check(&execution, &circuit).is_err());
    assert_eq!(initial, before);
}

#[test]
fn noncanonical_boolean_cell_read_after_write_rejects() {
    let plan = selected_plan(NONCANONICAL_PLAN);
    let valid = state(&plan);
    let StateValue::Array(array) = valid.get_ref() else {
        panic!("expected root state array")
    };
    let invalid_bool = StateValue::Cell(Sp::new(field_value(canonical_field("2").unwrap())));
    let array = array.clone().insert(2, invalid_bool).unwrap();
    let malformed = ChargedState::new(StateValue::Array(array));
    let before = malformed.clone();

    let result = prepare(
        &plan,
        &BTreeMap::new(),
        &malformed,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    );
    assert!(result.is_err());
    assert_eq!(malformed, before);
}
