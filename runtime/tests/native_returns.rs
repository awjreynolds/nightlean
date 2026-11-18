#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Execution, Expr, Plan, check, create_state, field_value, prepare, zkir::IrSource,
};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn fixture(entry: &str) -> (Plan, IrSource) {
    let (plan, circuit): (&str, &[u8]) = match entry {
        "readValues" => (
            include_str!("fixtures/native-returns/321/NativeReturns.readValues.impact.json"),
            include_bytes!("fixtures/native-returns/321/NativeReturns.readValues.zkir"),
        ),
        "advance" => (
            include_str!("fixtures/native-returns/321/NativeReturns.advance.impact.json"),
            include_bytes!("fixtures/native-returns/321/NativeReturns.advance.zkir"),
        ),
        _ => unreachable!(),
    };
    (
        serde_json::from_str(plan).unwrap(),
        IrSource::load(circuit).unwrap(),
    )
}

fn inputs(amount: u64, enabled: bool) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("amount".into(), json!(amount.to_string())),
        ("enabled".into(), json!(enabled)),
    ])
}

fn assert_returns(execution: &Execution, balance: u64, count: u64, enabled: bool) {
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("balanceValue".into(), json!(balance.to_string())),
            ("countValue".into(), json!(count.to_string())),
            ("enabledValue".into(), json!(enabled)),
        ])
    );
    let fields = [
        field_value(Fr::from(balance)),
        field_value(Fr::from(count)),
        field_value(Fr::from(u8::from(enabled))),
    ];
    let (commitment, randomness) = execution.preimage.communications_commitment.unwrap();
    let arguments = execution
        .preimage
        .inputs
        .iter()
        .copied()
        .map(field_value)
        .collect::<Vec<_>>();
    assert_eq!(
        commitment,
        onchain_runtime::communication_commitment(
            AlignedValue::concat(&arguments),
            AlignedValue::concat(&fields),
            randomness
        )
    );
}

#[test]
fn native_getter_results_bind_post_effect_values_and_reject_forgery() {
    let (getter, getter_circuit) = fixture("readValues");
    let state = create_state(
        &getter,
        &BTreeMap::from([
            ("balance".into(), json!("10")),
            ("count".into(), json!("0")),
        ]),
    )
    .unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let result = prepare(&getter, &inputs(0, true), &state, params, address).unwrap();
    check(&result, &getter_circuit).unwrap();
    assert_returns(&result, 10, 0, true);
    let mut state = state;
    let (advance, advance_circuit) = fixture("advance");
    for (amount, enabled, balance, count) in [(3, false, 13, 1), (4, true, 17, 2)] {
        let execution =
            prepare(&advance, &inputs(amount, enabled), &state, params, address).unwrap();
        check(&execution, &advance_circuit).unwrap();
        assert_eq!(execution.preimage.inputs, [Fr::from(amount)]);
        assert!(execution.preimage.private_transcript.is_empty());
        assert_returns(&execution, balance, count, enabled);
        if amount == 3 {
            let mut forged = execution.preimage.clone();
            forged.inputs[0] = Fr::from(amount + 1);
            let changed_argument = [field_value(Fr::from(amount + 1))];
            let output = [
                field_value(Fr::from(balance)),
                field_value(Fr::from(count)),
                field_value(Fr::from(u8::from(enabled))),
            ];
            let (_, randomness) = forged.communications_commitment.unwrap();
            forged.communications_commitment = Some((
                onchain_runtime::communication_commitment(
                    AlignedValue::concat(&changed_argument),
                    AlignedValue::concat(&output),
                    randomness,
                ),
                randomness,
            ));
            assert!(forged.check(&advance_circuit).is_err());
        }
        state = execution.after.state;
    }
    let mut result = prepare(&getter, &inputs(0, false), &state, params, address).unwrap();
    check(&result, &getter_circuit).unwrap();
    assert_returns(&result, 17, 2, false);
    let (_, randomness) = result.preimage.communications_commitment.unwrap();
    let forged_fields = [
        field_value(Fr::from(18u64)),
        field_value(Fr::from(2u64)),
        field_value(Fr::from(0u64)),
    ];
    result.preimage.communications_commitment = Some((
        onchain_runtime::communication_commitment(
            AlignedValue::concat(std::iter::empty::<&AlignedValue>()),
            AlignedValue::concat(&forged_fields),
            randomness,
        ),
        randomness,
    ));
    assert!(result.preimage.check(&getter_circuit).is_err());
    assert!(check(&result, &getter_circuit).is_err());
    let mut forged_plan = getter.clone();
    forged_plan.returns[0].expression = Expr::Constant {
        value: "999".into(),
    };
    let forged = prepare(&forged_plan, &inputs(0, false), &state, params, address).unwrap();
    assert!(forged.preimage.check(&getter_circuit).is_err());
    assert!(check(&forged, &getter_circuit).is_err());
    let mut mistyped = getter.clone();
    mistyped.returns[1].ty = "Native".into();
    assert!(prepare(&mistyped, &inputs(0, false), &state, params, address).is_err());
}
