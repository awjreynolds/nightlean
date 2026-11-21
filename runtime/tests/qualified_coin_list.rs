#![cfg(feature = "zkir-321")]

use anyhow::Context;
use base_crypto::{fab::AlignedValue, hash::HashOutput};
use coin_structure::{
    coin::{Info as ShieldedCoinInfo, Nonce, ShieldedTokenType},
    contract::ContractAddress,
    transfer::Recipient,
};
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::{context::QueryContext, state::StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_QUALIFIED_COIN_LIST_DIR")
        .map(PathBuf::from)
        .expect("NOCTIUM_QUALIFIED_COIN_LIST_DIR")
}

fn bytes(byte: u8) -> Json {
    json!({"kind": "bytes", "values": vec![byte; 32]})
}

fn inputs(nonce: u8, color: u8, amount: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("nonce".into(), bytes(nonce)),
        ("color".into(), bytes(color)),
        ("amount".into(), json!(amount.to_string())),
    ])
}

fn assert_coin_list(value: &StateValue<noctium_runtime::Db>, expected: &[AlignedValue]) {
    let StateValue::Array(node) = value else {
        panic!("expected native List array");
    };
    assert_eq!(node.len(), 3);
    let StateValue::Cell(length) = node.get(2).unwrap() else {
        panic!("expected List length Cell");
    };
    assert_eq!(**length, AlignedValue::from(expected.len() as u64));
    if let Some((head, tail)) = expected.split_first() {
        let StateValue::Cell(value) = node.get(0).unwrap() else {
            panic!("expected qualified coin head");
        };
        assert_eq!(**value, *head);
        assert_coin_list(node.get(1).unwrap(), tail);
    } else {
        assert!(matches!(node.get(0), Some(StateValue::Null)));
        assert!(matches!(node.get(1), Some(StateValue::Null)));
    }
}

#[test]
#[ignore = "requires fresh artifacts in NOCTIUM_QUALIFIED_COIN_LIST_DIR"]
fn push_front_coin_uses_current_booking_and_preserves_list_order() -> anyhow::Result<()> {
    let directory = artifacts();
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("QualifiedCoinList.pushFrontCoin.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("QualifiedCoinList.pushFrontCoin.zkir"),
    )?)?;
    let prior_coin = ShieldedCoinInfo {
        nonce: Nonce(HashOutput([4; 32])),
        type_: ShieldedTokenType(HashOutput([5; 32])),
        value: 9,
    };
    let initial = create_state(&plan, &BTreeMap::from([("coinList".into(), json!([]))]))?;
    let own = ContractAddress(HashOutput([9; 32]));
    let other = ContractAddress(HashOutput([8; 32]));
    let coin = ShieldedCoinInfo {
        nonce: Nonce(HashOutput([2; 32])),
        type_: ShieldedTokenType(HashOutput([1; 32])),
        value: 5,
    };
    let new_inputs = inputs(2, 1, 5);
    let context_with_booking = |state, coin: &ShieldedCoinInfo, recipient| {
        let mut context = QueryContext::new(state, own);
        if let Some(recipient) = recipient {
            context.call_context.com_indices = context
                .call_context
                .com_indices
                .insert(coin.commitment(&Recipient::Contract(recipient)), 42);
        }
        context
    };

    let prior_inputs = inputs(4, 5, 9);
    let seed_context = QueryContext::new(initial.clone(), own);
    let mut seed_context = seed_context;
    seed_context.call_context.com_indices = seed_context
        .call_context
        .com_indices
        .insert(prior_coin.commitment(&Recipient::Contract(own)), 17);
    let seed = prepare_with_context(
        &plan,
        &prior_inputs,
        seed_context,
        &ledger::structure::INITIAL_PARAMETERS,
    )
    .context("seed the existing qualified coin")?;
    assert_eq!(check(&seed, &circuit)?, seed.activity_schedule);

    let seed_state = seed.after.state;
    let execution = prepare_with_context(
        &plan,
        &new_inputs,
        context_with_booking(seed_state.clone(), &coin, Some(own)),
        &ledger::structure::INITIAL_PARAMETERS,
    )
    .context("prepend the new qualified coin")?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    let slot = plan
        .state
        .iter()
        .position(|declaration| declaration.name == "coinList")
        .expect("coinList state slot");
    let StateValue::Array(root) = execution.after.state.get_ref() else {
        panic!("expected native state slots");
    };
    assert_coin_list(
        root.get(slot).expect("coinList state"),
        &[
            AlignedValue::from(coin.qualify(42)),
            AlignedValue::from(prior_coin.qualify(17)),
        ],
    );
    assert_eq!(
        execution
            .after
            .effects
            .claimed_shielded_receives
            .iter()
            .count(),
        0
    );

    for recipient in [None, Some(other)] {
        let context = context_with_booking(seed_state.clone(), &coin, recipient);
        let error = prepare_with_context(
            &plan,
            &new_inputs,
            context.clone(),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .err()
        .expect("a booking for the current contract is required");
        assert!(
            error
                .to_string()
                .contains("absent from the current transaction")
        );
        assert_eq!(context.state, seed_state);
    }
    Ok(())
}
