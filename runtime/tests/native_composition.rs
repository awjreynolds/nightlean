#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{
    Plan,
    assembly::{CheckedNativeCall, partition_checked_two_call},
    check, create_state, prepare,
    zkir::IrSource,
};
use onchain_runtime::{
    context::QueryContext,
    state::{ChargedState, EntryPointBuf},
};
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
fn native_claim_partitions_one_checked_callee_and_skips_inactive_claims() {
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
    let checked = partition_checked_two_call(
        checked_call(
            &caller_execution,
            &caller_circuit,
            caller_state.clone(),
            caller_address,
            EntryPointBuf::from(b"claim".to_vec()),
            Fr::from(53u64),
        ),
        checked_call(
            &callee_execution,
            &callee_circuit,
            callee_state.clone(),
            callee_address,
            callee_entry.clone(),
            Fr::from(101u64),
        ),
        &INITIAL_PARAMETERS,
    )
    .unwrap();
    assert_eq!(checked.callee_preimage.inputs, [Fr::from(3u64)]);
    assert_eq!(checked.transcripts.len(), 2);
    assert_ne!(checked.caller_commitment, checked.callee_commitment);

    let wrong_tuple = prepare(
        &caller_plan,
        &caller_inputs(HashOutput([43; 32]), entry_hash, true),
        &caller_state,
        &INITIAL_PARAMETERS,
        caller_address,
    )
    .unwrap();
    assert!(
        partition_checked_two_call(
            checked_call(
                &wrong_tuple,
                &caller_circuit,
                caller_state.clone(),
                caller_address,
                EntryPointBuf::from(b"claim".to_vec()),
                Fr::from(53u64),
            ),
            checked_call(
                &callee_execution,
                &callee_circuit,
                callee_state.clone(),
                callee_address,
                callee_entry.clone(),
                Fr::from(101u64),
            ),
            &INITIAL_PARAMETERS,
        )
        .is_err()
    );

    let inactive = prepare(
        &caller_plan,
        &caller_inputs(callee_address.0, entry_hash, false),
        &caller_state,
        &INITIAL_PARAMETERS,
        caller_address,
    )
    .unwrap();
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
    let mut forged_inactive = inactive;
    forged_inactive.after.effects = caller_execution.after.effects.clone();
    let mut stale_context = QueryContext::new(caller_state, caller_address);
    stale_context.effects = caller_execution.after.effects.clone();
    assert!(
        partition_checked_two_call(
            CheckedNativeCall {
                execution: &forged_inactive,
                circuit: &caller_circuit,
                initial_context: stale_context,
                entry_point: EntryPointBuf::from(b"claim".to_vec()),
                communication_commitment_rand: Fr::from(53u64),
            },
            checked_call(
                &callee_execution,
                &callee_circuit,
                callee_state,
                callee_address,
                callee_entry,
                Fr::from(101u64),
            ),
            &INITIAL_PARAMETERS,
        )
        .is_err()
    );
}
