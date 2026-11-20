#![cfg(feature = "zkir-321")]

use base_crypto::cost_model::CostDuration;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::{context::QueryContext, ops::Op};
use serde_json::json;
use std::{collections::BTreeMap, fs, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires fresh Lean output via NOCTIUM_NATIVE_TEST_ARTIFACTS"]
fn checkpoint_binds_the_ordered_native_transcript() {
    let artifacts = PathBuf::from(std::env::var_os("NOCTIUM_NATIVE_TEST_ARTIFACTS").unwrap());
    let plan_bytes = fs::read(artifacts.join("NativeCheckpoint.apply.impact.json")).unwrap();
    let circuit_bytes = fs::read(artifacts.join("NativeCheckpoint.apply.zkir")).unwrap();
    let plan: Plan = serde_json::from_slice(&plan_bytes).unwrap();
    let circuit = IrSource::load(circuit_bytes.as_slice()).unwrap();
    let state = |first: &str, second: &str| {
        create_state(
            &plan,
            &BTreeMap::from([
                ("firstMark".into(), json!(first)),
                ("secondMark".into(), json!(second)),
            ]),
        )
        .unwrap()
    };
    let initial = state("0", "0");
    let expected = state("1", "2");
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    for enabled in [true, false] {
        let execution = prepare(
            &plan,
            &BTreeMap::from([("enabled".into(), json!(enabled))]),
            &initial,
            params,
            address,
        )
        .unwrap();
        assert_eq!(
            check(&execution, &circuit).unwrap(),
            execution.activity_schedule
        );
        assert_eq!(execution.after.state.get_ref(), expected.get_ref());
        assert_eq!(execution.returns_json()["current"], json!("2"));
        let ordered: Vec<_> = execution
            .program
            .iter()
            .filter(|op| matches!(op, Op::Ins { .. } | Op::Ckpt))
            .map(|op| matches!(op, Op::Ckpt))
            .collect();
        if enabled {
            assert_eq!(ordered, [false, true, false]);
            let mut preimage = execution.preimage;
            let marker = preimage
                .public_transcript_inputs
                .iter_mut()
                .find(|field| **field == Fr::from(0xffu64))
                .expect("the checkpoint is part of the public transcript");
            *marker = Fr::from(0u64);
            assert!(preimage.check(&circuit).is_err());
        } else {
            assert_eq!(ordered, [false, false]);
            assert!(execution.activity_schedule.contains(&Some(1)));
        }
    }

    // Keep the first write inside the pinned model's guaranteed budget.
    let mut limited = params.clone();
    limited.limits.time_to_dismiss_per_byte = CostDuration::ZERO;
    limited.limits.min_time_to_dismiss = CostDuration::from_picoseconds(8_835_000_000);
    let split = prepare(
        &plan,
        &BTreeMap::from([("enabled".into(), json!(true))]),
        &initial,
        &limited,
        address,
    )
    .unwrap();
    let guaranteed = split.guaranteed.as_ref().expect("guaranteed prefix");
    let fallible = split.fallible.as_ref().expect("fallible continuation");
    assert!(matches!(
        fallible.program.iter_deref().next(),
        Some(Op::Ckpt)
    ));
    let prefix = QueryContext::new(initial, address)
        .run_transcript(guaranteed, &limited.cost_model.runtime_cost_model)
        .unwrap();
    assert_eq!(prefix.context.state.get_ref(), state("1", "0").get_ref());
    assert_eq!(split.after.state.get_ref(), expected.get_ref());
    assert_eq!(check(&split, &circuit).unwrap(), split.activity_schedule);
}
