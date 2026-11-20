#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::{coin::PublicAddress, contract::ContractAddress};
use noctium_runtime::{
    Db, Instruction, Plan, check, create_state, prepare_with_context, zkir::IrSource,
};
use onchain_runtime::{context::QueryContext, state::ChargedState};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

fn fresh_artifacts() -> (Plan, IrSource) {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_SELF_DIR")
            .expect("set NOCTIUM_SELF_DIR to the fresh Lean emission directory"),
    );
    let plan: Plan = serde_json::from_slice(
        &fs::read(directory.join("NativeContractAddress.identify.impact.json"))
            .expect("fresh contract Impact plan exists"),
    )
    .expect("fresh contract Impact plan parses");
    let circuit = IrSource::load(
        fs::File::open(directory.join("NativeContractAddress.identify.zkir"))
            .expect("fresh contract ZKIR exists"),
    )
    .expect("fresh contract ZKIR parses");
    (plan, circuit)
}

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn state(plan: &Plan, address: &[u8; 32]) -> ChargedState<Db> {
    create_state(
        plan,
        &BTreeMap::from([("lastAddress".into(), bytes(address))]),
    )
    .expect("source state creates the lastAddress cell")
}

#[test]
#[ignore = "requires fresh Lean output in NOCTIUM_SELF_DIR"]
fn own_address_comes_from_context_binds_proof_and_writes_guarded_state() {
    let (plan, circuit) = fresh_artifacts();
    assert!(plan.operations.iter().any(|operation| matches!(
        operation,
        Instruction::Guarded { operation, .. }
            if matches!(operation.as_ref(), Instruction::ReadContractAddress { destination } if destination == "own")
    )));

    let params = &ledger::structure::INITIAL_PARAMETERS;
    let zero = [0; 32];
    let initial = state(&plan, &zero);
    let first = ContractAddress(HashOutput(std::array::from_fn(|index| index as u8)));
    let second = ContractAddress(HashOutput([0xff; 32]));
    let caller = ContractAddress(HashOutput([0x51; 32]));

    for (address, enabled) in [
        (first, true),
        (first, false),
        (second, true),
        (second, false),
    ] {
        let mut context = QueryContext::new(initial.clone(), address);
        context.call_context.caller = Some(PublicAddress::Contract(caller));
        let execution = prepare_with_context(
            &plan,
            &BTreeMap::from([("enabled".into(), json!(enabled))]),
            context,
            params,
        )
        .expect("source operations pass native preparation");
        assert_eq!(
            check(&execution, &circuit).unwrap(),
            execution.activity_schedule
        );

        let expected = if enabled { address.0.0 } else { zero };
        assert_eq!(
            execution.returns_json()["address"],
            bytes(&expected),
            "the result follows the contract context, not the caller"
        );
        assert_eq!(execution.after.state, state(&plan, &expected));

        if enabled {
            let wrong = if address == first { second } else { first };
            assert!(
                QueryContext::new(initial.clone(), wrong)
                    .query(
                        &execution.program,
                        None,
                        &params.cost_model.runtime_cost_model
                    )
                    .is_err(),
                "an execution for another contract address must fail"
            );

            let mut altered = execution.preimage.clone();
            let last = altered
                .public_transcript_outputs
                .last_mut()
                .expect("the native proof has a public output");
            *last = *last + Fr::from(1u64);
            assert!(altered.check(&circuit).is_err());
        } else {
            assert!(
                execution
                    .activity_schedule
                    .windows(3)
                    .any(|groups| { groups == [Some(1), Some(4), Some(5)] })
            );
        }
    }
}
