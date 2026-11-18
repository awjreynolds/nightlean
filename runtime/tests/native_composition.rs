#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use ledger::structure::{INITIAL_PARAMETERS, ProofPreimageVersioned};
use noctium_runtime::{
    Plan,
    assembly::{CheckedNativeCall, assemble_checked_calls},
    check, create_state, prepare,
    zkir::IrSource,
};
use onchain_runtime::{
    context::QueryContext,
    state::{ChargedState, EntryPointBuf},
};
use rand::rngs::OsRng;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn caller_fixture() -> (Plan, IrSource) {
    (
        serde_json::from_str(include_str!(
            "fixtures/native-call-claims/321/NativeCallClaims.claim.impact.json"
        ))
        .unwrap(),
        IrSource::load(
            include_bytes!("fixtures/native-call-claims/321/NativeCallClaims.claim.zkir")
                .as_slice(),
        )
        .unwrap(),
    )
}

fn callee_fixture() -> (Plan, IrSource) {
    (
        serde_json::from_str(include_str!(
            "fixtures/native-returns/321/NativeReturns.advance.impact.json"
        ))
        .unwrap(),
        IrSource::load(
            include_bytes!("fixtures/native-returns/321/NativeReturns.advance.zkir").as_slice(),
        )
        .unwrap(),
    )
}

fn bytes32(value: HashOutput) -> Json {
    json!({"kind":"bytes", "values":value.0})
}

fn caller_inputs(
    target: HashOutput,
    entry_hash: HashOutput,
    enabled: bool,
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("target".into(), bytes32(target)),
        ("entryHash".into(), bytes32(entry_hash)),
        ("enabled".into(), json!(enabled)),
        ("opening".into(), json!("101")),
        ("argument".into(), json!("3")),
        ("expectedBalance".into(), json!("13")),
        ("expectedCount".into(), json!("1")),
        ("expectedEnabled".into(), json!(false)),
    ])
}

fn callee_inputs() -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("amount".into(), json!("3")),
        ("enabled".into(), json!(false)),
    ])
}

fn checked_call<'a>(
    execution: &'a noctium_runtime::Execution,
    circuit: &'a IrSource,
    state: ChargedState<noctium_runtime::Db>,
    address: ContractAddress,
    entry_point: EntryPointBuf,
    randomness: Fr,
) -> CheckedNativeCall<'a> {
    CheckedNativeCall {
        execution,
        circuit,
        initial_context: QueryContext::new(state, address),
        entry_point,
        communication_commitment_rand: randomness,
    }
}

#[test]
fn native_intent_assembles_a_call_forest_and_rejects_unmatched_claims() {
    let (caller_plan, caller_circuit) = caller_fixture();
    let (callee_plan, callee_circuit) = callee_fixture();
    let caller_address = ContractAddress(HashOutput([7; 32]));
    let callee_address = ContractAddress(HashOutput([42; 32]));
    let caller_state = create_state(
        &caller_plan,
        &BTreeMap::from([("marker".into(), json!("9"))]),
    )
    .unwrap();
    let callee_state = create_state(
        &callee_plan,
        &BTreeMap::from([
            ("balance".into(), json!("10")),
            ("count".into(), json!("0")),
        ]),
    )
    .unwrap();
    let callee_entry = EntryPointBuf::from(b"advance".to_vec());
    let callee_execution = prepare(
        &callee_plan,
        &callee_inputs(),
        &callee_state,
        &INITIAL_PARAMETERS,
        callee_address,
    )
    .unwrap();
    check(&callee_execution, &callee_circuit).unwrap();
    assert_eq!(
        callee_execution.returns_json(),
        BTreeMap::from([
            ("balanceValue".into(), json!("13")),
            ("countValue".into(), json!("1")),
            ("enabledValue".into(), json!(false)),
        ])
    );

    let entry_hash = callee_entry.ep_hash();
    let caller_execution = prepare(
        &caller_plan,
        &caller_inputs(callee_address.0, entry_hash, true),
        &caller_state,
        &INITIAL_PARAMETERS,
        caller_address,
    )
    .unwrap();
    assert_eq!(caller_execution.after.state, caller_state);
    assert_eq!(
        caller_execution.returns_json(),
        BTreeMap::from([("didClaim".into(), json!(true))])
    );
    let callee = || {
        checked_call(
            &callee_execution,
            &callee_circuit,
            callee_state.clone(),
            callee_address,
            callee_entry.clone(),
            Fr::from(101u64),
        )
    };
    let caller = |execution| {
        checked_call(
            execution,
            &caller_circuit,
            caller_state.clone(),
            caller_address,
            EntryPointBuf::from(b"claim".to_vec()),
            Fr::from(53u64),
        )
    };
    let assemble = |calls: &[CheckedNativeCall<'_>]| {
        assemble_checked_calls(calls, &INITIAL_PARAMETERS, 1_800_000_000, &mut OsRng)
    };
    let independent_address = ContractAddress(HashOutput([12; 32]));
    let independent_execution = prepare(
        &callee_plan,
        &callee_inputs(),
        &callee_state,
        &INITIAL_PARAMETERS,
        independent_address,
    )
    .unwrap();
    let independent = || {
        checked_call(
            &independent_execution,
            &callee_circuit,
            callee_state.clone(),
            independent_address,
            callee_entry.clone(),
            Fr::from(102u64),
        )
    };
    let intent = assemble(&[caller(&caller_execution), callee(), independent()]).unwrap();
    let assembled: Vec<_> = intent.calls().collect();
    assert_eq!(
        assembled.iter().map(|c| c.address).collect::<Vec<_>>(),
        [caller_address, callee_address, independent_address]
    );
    let ProofPreimageVersioned::V2(preimage) = &assembled[1].proof else {
        panic!("expected a V2 preimage");
    };
    assert_eq!(preimage.inputs, [Fr::from(3u64)]);
    assert_eq!(
        preimage.key_location.0,
        format!("{}:advance", hex::encode(callee_address.0.0))
    );
    assert!(assembled[0].calls(assembled[1]));
    assert!(!assembled[0].calls(assembled[2]));
    assert!(assemble(&[callee(), caller(&caller_execution)]).is_err());
    assert!(assemble(&[caller(&caller_execution)]).is_err());
    assert!(assemble(&[callee(), callee()]).is_err());

    let wrong_tuple = prepare(
        &caller_plan,
        &caller_inputs(HashOutput([43; 32]), entry_hash, true),
        &caller_state,
        &INITIAL_PARAMETERS,
        caller_address,
    )
    .unwrap();
    assert!(assemble(&[caller(&wrong_tuple), callee()]).is_err());

    let prepare_inactive = || {
        prepare(
            &caller_plan,
            &caller_inputs(callee_address.0, entry_hash, false),
            &caller_state,
            &INITIAL_PARAMETERS,
            caller_address,
        )
        .unwrap()
    };
    let inactive = prepare_inactive();
    check(&inactive, &caller_circuit).unwrap();
    assert!(inactive.after.effects.claimed_contract_calls.is_empty());
    assert_eq!(
        inactive.returns_json(),
        BTreeMap::from([("didClaim".into(), json!(false))])
    );
    assert_eq!(
        inactive
            .activity_schedule
            .iter()
            .filter_map(|skip| *skip)
            .collect::<Vec<_>>(),
        [1, 4, 1, 1, 11, 2, 2, 1, 1]
    );
    assert!(assemble(&[caller(&inactive)]).is_ok());

    let mut forged_inactive = prepare_inactive();
    forged_inactive.after.effects = caller_execution.after.effects.clone();
    let mut forged = caller(&forged_inactive);
    forged.initial_context.effects = caller_execution.after.effects.clone();
    assert!(assemble(&[forged, callee()]).is_err());
}
