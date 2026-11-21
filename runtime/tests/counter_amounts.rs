#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Expr, ImmediateAmount, Instruction, Plan, check, create_state, prepare, zkir::IrSource,
};
use onchain_runtime::{ops::Op, state::{ChargedState, StateValue}};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env,
    path::{Path, PathBuf},
};

fn artifacts() -> PathBuf {
    env::var_os("NOCTIUM_COUNTER_AMOUNTS_DIR")
        .map(PathBuf::from)
        .expect("set fresh outputs in NOCTIUM_COUNTER_AMOUNTS_DIR")
}

fn fixture(directory: &Path, entry: &str) -> (Plan, IrSource) {
    let stem = format!("CounterAmounts.{entry}");
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit = IrSource::load(
        std::fs::read(directory.join(format!("{stem}.zkir")))
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    (plan, circuit)
}

fn inputs(plan: &Plan, owner: u8, spender: u8, amount: u64, enabled: bool) -> BTreeMap<String, Json> {
    plan.circuit
        .inputs
        .iter()
        .map(|input| {
            let value = match input.name.as_str() {
                "owner" => json!({"kind":"bytes", "values":vec![owner; 32]}),
                "spender" => json!({"kind":"bytes", "values":vec![spender; 32]}),
                "amount" => json!(amount.to_string()),
                "enabled" => json!(enabled),
                other => panic!("unexpected input {other}"),
            };
            (input.name.clone(), value)
        })
        .collect()
}

fn total(state: &ChargedState<Db>) -> AlignedValue {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let StateValue::Cell(value) = slots.get(0).unwrap() else {
        panic!("expected standalone Counter cell")
    };
    (**value).clone()
}

fn epoch(state: &ChargedState<Db>, owner: u8, spender: u8) -> AlignedValue {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let StateValue::Map(owners) = slots.get(1).unwrap() else {
        panic!("expected owner map")
    };
    let owner_key: AlignedValue = [owner; 32].into();
    let StateValue::Map(spenders) = &*owners.get(&owner_key).unwrap() else {
        panic!("expected spender map")
    };
    let spender_key: AlignedValue = [spender; 32].into();
    let StateValue::Cell(value) = &*spenders.get(&spender_key).unwrap() else {
        panic!("expected nested Counter cell")
    };
    (**value).clone()
}

fn assert_amount_immediate(execution: &noctium_runtime::Execution, amount: u64, subtract: bool) {
    let immediates = execution
        .program
        .iter()
        .filter(|operation| match (operation, subtract) {
            (Op::Addi { immediate }, false) | (Op::Subi { immediate }, true) => {
                *immediate == amount as u32
            }
            _ => false,
        })
        .count();
    assert_eq!(immediates, 2, "one native immediate per Counter update");
    let counter_updates = execution
        .program
        .iter()
        .filter(|operation| matches!(operation, Op::Addi { .. } | Op::Subi { .. }))
        .count();
    assert_eq!(counter_updates, 2, "each source update uses one native opcode");
}

#[test]
#[ignore = "requires fresh CounterAmounts ledger outputs in NOCTIUM_COUNTER_AMOUNTS_DIR"]
fn counter_amounts_bind_dynamic_u16_updates_on_standalone_and_nested_paths() {
    let directory = artifacts();
    let (apply, apply_circuit) = fixture(&directory, "apply");
    let (reduce, reduce_circuit) = fixture(&directory, "reduce");
    let (guarded, guarded_circuit) = fixture(&directory, "guarded");
    let initial = create_state(
        &apply,
        &BTreeMap::from([("total".into(), json!("10")), ("epochs".into(), json!([]))]),
    )
    .unwrap();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    let mut state = initial.clone();
    for (entry, circuit, subtract, amount, expected_total, expected_epoch) in [
        ("apply", &apply_circuit, false, 0u64, 10u64, 0u64),
        ("apply", &apply_circuit, false, 3u64, 13u64, 3u64),
        ("reduce", &reduce_circuit, true, 2u64, 11u64, 1u64),
    ] {
        let plan = match entry {
            "apply" => &apply,
            "reduce" => &reduce,
            _ => unreachable!(),
        };
        let before = state.clone();
        let execution = prepare(
            plan,
            &inputs(plan, 4, 7, amount, true),
            &before,
            parameters,
            address,
        )
        .unwrap();
        check(&execution, circuit).unwrap();
        assert_amount_immediate(&execution, amount, subtract);
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([
                ("totalValue".into(), json!(expected_total.to_string())),
                ("epochValue".into(), json!(expected_epoch.to_string())),
            ])
        );
        state = execution.after.state;
        assert_eq!(total(&state), AlignedValue::from(expected_total));
        assert_eq!(epoch(&state, 4, 7), AlignedValue::from(expected_epoch));

        if amount == 3 {
            let mut tampered = apply.clone();
            let amount = tampered
                .operations
                .iter_mut()
                .find_map(|operation| match operation {
                    Instruction::AddImmediate { amount } => Some(amount),
                    _ => None,
                })
                .expect("source plan has a standalone increment");
            *amount = ImmediateAmount::Expression(Expr::Uint {
                maximum: u16::MAX.to_string(),
                value: "4".into(),
            });
            let dishonest = prepare(
                &tampered,
                &inputs(&tampered, 4, 7, 3, true),
                &before,
                parameters,
                address,
            )
            .expect("tampered amount still prepares against the same input");
            assert!(check(&dishonest, circuit).is_err());
        }
    }

    let max_state = create_state(
        &apply,
        &BTreeMap::from([("total".into(), json!("0")), ("epochs".into(), json!([]))]),
    )
    .unwrap();
    let maximum = prepare(
        &apply,
        &inputs(&apply, 4, 7, u16::MAX as u64, true),
        &max_state,
        parameters,
        address,
    )
    .unwrap();
    check(&maximum, &apply_circuit).unwrap();
    assert_amount_immediate(&maximum, u16::MAX as u64, false);
    assert_eq!(total(&maximum.after.state), AlignedValue::from(u16::MAX as u64));
    assert_eq!(epoch(&maximum.after.state, 4, 7), AlignedValue::from(u16::MAX as u64));

    assert!(prepare(
        &apply,
        &inputs(&apply, 4, 7, u16::MAX as u64 + 1, true),
        &max_state,
        parameters,
        address,
    )
    .is_err());

    let zero_state = create_state(
        &apply,
        &BTreeMap::from([("total".into(), json!("0")), ("epochs".into(), json!([]))]),
    )
    .unwrap();
    let seeded = prepare(
        &apply,
        &inputs(&apply, 4, 7, 0, true),
        &zero_state,
        parameters,
        address,
    )
    .unwrap()
    .after
    .state;
    assert!(prepare(
        &reduce,
        &inputs(&reduce, 4, 7, 1, true),
        &seeded,
        parameters,
        address,
    )
    .is_err());

    let inactive = prepare(
        &guarded,
        &inputs(&guarded, 8, 9, 7, false),
        &zero_state,
        parameters,
        address,
    )
    .unwrap();
    check(&inactive, &guarded_circuit).unwrap();
    assert_eq!(inactive.after.state, zero_state);
    assert!(!inactive
        .program
        .iter()
        .any(|operation| matches!(operation, Op::Addi { .. } | Op::Subi { .. })));
}
