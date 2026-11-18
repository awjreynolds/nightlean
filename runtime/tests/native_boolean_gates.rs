#![cfg(feature = "zkir-321")]

use noctium_runtime::zkir::IrSource;
use noctium_runtime::{Expr, Plan, check, create_state, prepare};
use serde_json::json;
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

#[test]
fn typed_boolean_gates_bind_truth_tables_and_eager_assertions() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/boolean-gates/321/BooleanGates.truthTable.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/boolean-gates/321/BooleanGates.truthTable.zkir").as_slice(),
    )
    .unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    for left in [false, true] {
        for right in [false, true] {
            let inputs =
                BTreeMap::from([("left".into(), json!(left)), ("right".into(), json!(right))]);
            let execution = prepare(
                &plan,
                &inputs,
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )
            .unwrap();
            check(&execution, &circuit).unwrap();
            assert_eq!(
                execution.returns_json(),
                BTreeMap::from([
                    ("andResult".into(), json!(left && right)),
                    ("orResult".into(), json!(left || right)),
                    ("xorResult".into(), json!(left ^ right)),
                    ("xorThreeResult".into(), json!(left ^ right ^ true)),
                ])
            );
            let mut forged = plan.clone();
            forged.returns[0].expression = Expr::Bool {
                value: !(left && right),
            };
            let forged = prepare(
                &forged,
                &inputs,
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )
            .unwrap();
            assert!(check(&forged, &circuit).is_err());
        }
    }
    for (plan_json, circuit_json, name, expected) in [
        (
            include_str!("fixtures/boolean-gates/321/BooleanGates.andEager.impact.json"),
            include_bytes!("fixtures/boolean-gates/321/BooleanGates.andEager.zkir").as_slice(),
            "andGuardResult",
            false,
        ),
        (
            include_str!("fixtures/boolean-gates/321/BooleanGates.orEager.impact.json"),
            include_bytes!("fixtures/boolean-gates/321/BooleanGates.orEager.zkir").as_slice(),
            "orGuardResult",
            true,
        ),
    ] {
        let plan: Plan = serde_json::from_str(plan_json).unwrap();
        let circuit = IrSource::load(circuit_json).unwrap();
        let initial = create_state(&plan, &BTreeMap::new()).unwrap();
        let mut execution = prepare(
            &plan,
            &BTreeMap::from([("enabled".into(), json!(true))]),
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        assert_eq!(execution.returns_json()[name], json!(expected));
        execution.preimage.private_transcript[0] = Fr::from(0u64);
        assert!(check(&execution, &circuit).is_err());
        assert!(
            prepare(
                &plan,
                &BTreeMap::from([("enabled".into(), json!(false))]),
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )
            .is_err()
        );
    }
}
