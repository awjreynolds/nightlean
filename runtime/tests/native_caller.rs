#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::{
    coin::{PublicAddress, UserAddress},
    contract::ContractAddress,
};
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::context::QueryContext;
use serde_json::json;
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires fresh NativeCaller.lookup artifacts in NOCTIUM_CALLER_DIR"]
fn caller_presence_kind_address_and_guard_bind_to_native_context() {
    let directory = PathBuf::from(std::env::var_os("NOCTIUM_CALLER_DIR").unwrap());
    let plan: Plan = serde_json::from_slice(
        &fs::read(directory.join("NativeCaller.lookup.impact.json")).unwrap(),
    )
    .unwrap();
    let circuit =
        IrSource::load(fs::File::open(directory.join("NativeCaller.lookup.zkir")).unwrap())
            .unwrap();
    let state = create_state(&plan, &BTreeMap::from([("recorded".into(), json!(true))])).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let bytes = std::array::from_fn(|index| (index + 1) as u8);
    let contract = PublicAddress::Contract(ContractAddress(HashOutput(bytes)));
    let user = PublicAddress::User(UserAddress(HashOutput(bytes)));
    let context = |caller| {
        let mut context = QueryContext::new(state.clone(), ContractAddress::default());
        context.call_context.caller = caller;
        context
    };
    let address_json =
        |selected| json!({"kind":"bytes", "values": if selected {bytes} else {[0; 32]}});

    for caller in [None, Some(contract), Some(user)] {
        for enabled in [true, false] {
            let execution = prepare_with_context(
                &plan,
                &BTreeMap::from([("enabled".into(), json!(enabled))]),
                context(caller),
                params,
            )
            .unwrap();
            assert_eq!(
                check(&execution, &circuit).unwrap(),
                execution.activity_schedule
            );
            let returns = execution.returns_json();
            let is_contract = enabled && caller == Some(contract);
            assert_eq!(returns["hasCaller"], json!(enabled && caller.is_some()));
            assert_eq!(returns["contractCaller"], json!(is_contract));
            assert_eq!(returns["callerContract"], address_json(is_contract));
            assert_eq!(
                returns["callerUser"],
                address_json(enabled && caller == Some(user))
            );

            let expected_state = create_state(
                &plan,
                &BTreeMap::from([("recorded".into(), json!(!enabled || caller.is_some()))]),
            )
            .unwrap();
            assert_eq!(execution.after.state.get_ref(), expected_state.get_ref());

            let changed_caller = if caller == Some(contract) {
                user
            } else {
                contract
            };
            assert_eq!(
                context(Some(changed_caller))
                    .query(
                        &execution.program,
                        None,
                        &params.cost_model.runtime_cost_model,
                    )
                    .is_err(),
                enabled
            );
            if enabled {
                let mut changed = execution.preimage;
                let caller_output = changed.public_transcript_outputs.last_mut().unwrap();
                *caller_output = *caller_output + Fr::from(1u64);
                assert!(changed.check(&circuit).is_err());
            }
        }
    }
}
