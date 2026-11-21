#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::{
    coin::{PublicAddress, TokenType, UnshieldedTokenType, UserAddress},
    contract::ContractAddress,
};
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::context::{ClaimedUnshieldedSpendsKey, QueryContext};
use serde_json::json;
use std::{collections::BTreeMap, fs::File, path::PathBuf};
use transient_crypto::curve::Fr;

#[test]
#[ignore = "requires generated artifacts in NOCTIUM_UNSHIELDED_SEND_DIR"]
fn unshielded_send_credits_only_the_current_contract() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_UNSHIELDED_SEND_DIR").expect("NOCTIUM_UNSHIELDED_SEND_DIR"),
    );
    let plan: Plan = serde_json::from_reader(File::open(
        directory.join("NativeUnshieldedSend.send.impact.json"),
    )?)?;
    let circuit = IrSource::load(File::open(
        directory.join("NativeUnshieldedSend.send.zkir"),
    )?)?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let own = ContractAddress(HashOutput([9; 32]));
    let context = QueryContext::new(create_state(&plan, &BTreeMap::new())?, own);
    let color = HashOutput(std::array::from_fn(|index| (index + 1) as u8));
    let token = TokenType::Unshielded(UnshieldedTokenType(color));

    for (is_contract, recipient_byte, self_credit) in
        [(true, 9, true), (true, 23, false), (false, 9, false)]
    {
        let recipient = HashOutput([recipient_byte; 32]);
        let inputs = BTreeMap::from([
            ("color".into(), json!({"kind": "bytes", "values": color.0})),
            ("amount".into(), json!("7")),
            ("isContract".into(), json!(is_contract)),
            (
                "recipient".into(),
                json!({"kind": "bytes", "values": recipient.0}),
            ),
        ]);
        let mut execution = prepare_with_context(&plan, &inputs, context.clone(), params)?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        let effects = context
            .query(
                &execution.program,
                None,
                &params.cost_model.runtime_cost_model,
            )?
            .context
            .effects;
        let target = if is_contract {
            PublicAddress::Contract(ContractAddress(recipient))
        } else {
            PublicAddress::User(UserAddress(recipient))
        };
        assert_eq!(
            effects.unshielded_inputs.iter().count(),
            usize::from(self_credit)
        );
        assert_eq!(
            effects.unshielded_inputs.get(&token).map(|value| *value),
            self_credit.then_some(7)
        );
        assert_eq!(effects.unshielded_outputs.iter().count(), 1);
        assert_eq!(
            effects.unshielded_outputs.get(&token).map(|value| *value),
            Some(7)
        );
        assert_eq!(effects.claimed_unshielded_spends.iter().count(), 1);
        assert_eq!(
            effects
                .claimed_unshielded_spends
                .get(&ClaimedUnshieldedSpendsKey(token, target))
                .map(|value| *value),
            Some(7)
        );

        if self_credit {
            // The public prologue reads the type tag after the two color fields and amount.
            assert_eq!(
                execution.preimage.public_transcript_outputs[3],
                Fr::from(1u64)
            );
            execution.preimage.public_transcript_outputs[3] = Fr::from(0u64);
            assert!(check(&execution, &circuit).is_err());
        }
    }
    Ok(())
}
