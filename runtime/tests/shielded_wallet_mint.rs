#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::{
    coin::{Info, Nonce, PublicKey},
    contract::ContractAddress,
    transfer::Recipient,
};
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::{context::QueryContext, state::StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs::File, path::PathBuf};

fn bytes(value: &[u8]) -> Json {
    json!({"kind": "bytes", "values": value})
}

#[test]
#[ignore = "requires fresh Lean output in NOCTIUM_WALLET_MINT_DIR"]
fn wallet_mint_binds_the_returned_coin_to_the_booked_wallet_output() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_WALLET_MINT_DIR").expect("NOCTIUM_WALLET_MINT_DIR"),
    );
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("ShieldedWalletMint.mintToWallet.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("ShieldedWalletMint.mintToWallet.zkir"),
    )?)?;
    let domain = HashOutput([3; 32]);
    let nonce = Nonce(HashOutput([2; 32]));
    let recipient = PublicKey(HashOutput([4; 32]));
    let address = ContractAddress(HashOutput([9; 32]));
    let coin = Info {
        nonce,
        type_: address.custom_shielded_token_type(domain),
        value: 5,
    };
    let inputs = || {
        BTreeMap::from([
            ("domain".into(), bytes(&domain.0)),
            ("nonce".into(), bytes(&nonce.0.0)),
            ("amount".into(), json!(coin.value.to_string())),
            ("recipient".into(), bytes(&recipient.0.0)),
        ])
    };
    let initial_cell = json!({
        "nonce": bytes(&[0; 32]),
        "color": bytes(&[0; 32]),
        "value": "0",
        "mtIndex": "0"
    });
    let state = create_state(&plan, &BTreeMap::from([("minted".into(), initial_cell)]))?;
    let commitment = coin.commitment(&Recipient::User(recipient));
    let context = || {
        let mut context = QueryContext::new(state.clone(), address);
        context.call_context.com_indices = context.call_context.com_indices.insert(commitment, 42);
        context
    };

    let execution = prepare_with_context(
        &plan,
        &inputs(),
        context(),
        &ledger::structure::INITIAL_PARAMETERS,
    )?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("coinNonce".into(), bytes(&nonce.0.0)),
            ("color".into(), bytes(&coin.type_.0.0)),
            ("value".into(), json!(coin.value.to_string())),
        ])
    );
    let StateValue::Array(slots) = execution.after.state.get_ref() else {
        anyhow::bail!("expected root state array")
    };
    let Some(StateValue::Cell(stored)) = slots.get(0) else {
        anyhow::bail!("expected minted wallet coin Cell")
    };
    assert_eq!(
        &**stored,
        &base_crypto::fab::AlignedValue::from(coin.qualify(42))
    );
    assert_eq!(execution.after.effects.shielded_mints.size(), 1);
    assert_eq!(
        execution
            .after
            .effects
            .shielded_mints
            .get(&domain)
            .map(|value| *value),
        Some(coin.value as u64)
    );
    assert_eq!(execution.after.effects.claimed_shielded_receives.size(), 0);

    let changed_recipient = PublicKey(HashOutput([5; 32]));
    let mut changed_inputs = inputs();
    changed_inputs.insert("recipient".into(), bytes(&changed_recipient.0.0));
    assert!(
        prepare_with_context(
            &plan,
            &changed_inputs,
            context(),
            &ledger::structure::INITIAL_PARAMETERS
        )
        .is_err()
    );
    Ok(())
}
