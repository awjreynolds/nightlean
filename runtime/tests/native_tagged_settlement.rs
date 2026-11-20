#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::{
    coin::{PublicAddress, ShieldedTokenType, TokenType, UnshieldedTokenType, UserAddress},
    contract::ContractAddress,
};
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::context::{ClaimedUnshieldedSpendsKey, QueryContext};
use serde_json::json;
use std::{collections::BTreeMap, fs, path::PathBuf};

#[test]
#[ignore = "requires generated NativeTaggedSettlement artifacts in NOCTIUM_SETTLEMENT_DIR"]
fn tagged_settlement_effects_bind_to_token_and_recipient() -> anyhow::Result<()> {
    let directory =
        PathBuf::from(std::env::var_os("NOCTIUM_SETTLEMENT_DIR").expect("NOCTIUM_SETTLEMENT_DIR"));
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join("NativeTaggedSettlement.record.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("NativeTaggedSettlement.record.zkir"),
    )?)?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let color = HashOutput(std::array::from_fn(|index| (index + 1) as u8));
    let recipient = HashOutput([23; 32]);
    let context = QueryContext::new(
        create_state(&plan, &BTreeMap::new())?,
        ContractAddress(HashOutput([9; 32])),
    );
    let prepare = |amount: u128, extra: u128, is_unshielded, is_contract, enabled, add_second| {
        let inputs = BTreeMap::from([
            ("color".into(), json!({"kind": "bytes", "values": color.0})),
            ("amount".into(), json!(amount.to_string())),
            ("extra".into(), json!(extra.to_string())),
            ("isUnshielded".into(), json!(is_unshielded)),
            ("isContract".into(), json!(is_contract)),
            (
                "recipient".into(),
                json!({"kind": "bytes", "values": recipient.0}),
            ),
            ("enabled".into(), json!(enabled)),
            ("addSecond".into(), json!(add_second)),
        ]);
        prepare_with_context(&plan, &inputs, context.clone(), params)
    };
    let execute = |amount, extra, is_unshielded, is_contract, enabled, add_second| {
        let execution = prepare(
            amount,
            extra,
            is_unshielded,
            is_contract,
            enabled,
            add_second,
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        let effects = context
            .query(
                &execution.program,
                None,
                &params.cost_model.runtime_cost_model,
            )?
            .context
            .effects;
        Ok::<_, anyhow::Error>((execution, effects))
    };

    let unshielded = TokenType::Unshielded(UnshieldedTokenType(color));
    let shielded = TokenType::Shielded(ShieldedTokenType(color));
    for (is_unshielded, is_contract, enabled, add_second, expected) in [
        (true, true, true, true, Some(10u128)),
        (false, false, true, true, Some(10u128)),
        (true, false, false, true, Some(3u128)),
        (false, true, false, false, None),
    ] {
        let (_, effects) = execute(7, 3, is_unshielded, is_contract, enabled, add_second)?;
        let selected = if is_unshielded { unshielded } else { shielded };
        let other = if is_unshielded { shielded } else { unshielded };
        assert_eq!(
            effects
                .unshielded_inputs
                .get(&selected)
                .map(|amount| *amount),
            expected
        );
        assert_eq!(
            effects
                .unshielded_outputs
                .get(&selected)
                .map(|amount| *amount),
            expected
        );
        assert_eq!(
            effects.unshielded_inputs.get(&other).map(|amount| *amount),
            None
        );
        assert_eq!(
            effects.unshielded_outputs.get(&other).map(|amount| *amount),
            None
        );
        assert_eq!(
            effects.unshielded_inputs.iter().count(),
            usize::from(expected.is_some())
        );
        assert_eq!(
            effects.unshielded_outputs.iter().count(),
            usize::from(expected.is_some())
        );
        let address = if is_contract {
            PublicAddress::Contract(ContractAddress(recipient))
        } else {
            PublicAddress::User(UserAddress(recipient))
        };
        let claim = ClaimedUnshieldedSpendsKey(selected, address);
        assert_eq!(
            effects
                .claimed_unshielded_spends
                .get(&claim)
                .map(|amount| *amount),
            expected
        );
        assert_eq!(
            effects.claimed_unshielded_spends.iter().count(),
            usize::from(expected.is_some())
        );
    }

    let (_, wide_effects) = execute(u128::MAX, 0, true, true, true, false)?;
    assert_eq!(
        wide_effects
            .unshielded_inputs
            .get(&unshielded)
            .map(|amount| *amount),
        Some(u128::MAX)
    );
    assert_eq!(
        wide_effects
            .unshielded_outputs
            .get(&unshielded)
            .map(|amount| *amount),
        Some(u128::MAX)
    );
    let wide_claim = ClaimedUnshieldedSpendsKey(
        unshielded,
        PublicAddress::Contract(ContractAddress(recipient)),
    );
    assert_eq!(
        wide_effects
            .claimed_unshielded_spends
            .get(&wide_claim)
            .map(|amount| *amount),
        Some(u128::MAX)
    );

    assert!(prepare(u64::MAX.into(), 1, true, true, true, true).is_err());
    assert!(prepare(u128::MAX, 0, true, true, true, true).is_err());
    Ok(())
}
