#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use noctium_runtime::{
    Plan, PreparationCursor, PreparationStep, check, create_state, prepare_with_context,
    zkir::IrSource,
};
use onchain_runtime::context::QueryContext;
use serde_json::json;
use std::{collections::BTreeMap, fs, path::PathBuf};

#[test]
#[ignore = "requires generated NativeStandaloneMints artifacts in NOCTIUM_STANDALONE_MINTS_DIR"]
fn standalone_mints_bind_uint64_amount_and_the_correct_namespace() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_STANDALONE_MINTS_DIR").expect("NOCTIUM_STANDALONE_MINTS_DIR"),
    );
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join("NativeStandaloneMints.record.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("NativeStandaloneMints.record.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let domain = HashOutput(std::array::from_fn(|index| index as u8));
    let context = QueryContext::new(state.clone(), ContractAddress::default());
    let prepare = |amount: u64, enabled, add_second| {
        let inputs = BTreeMap::from([
            ("domain".into(), json!({"kind":"bytes", "values":domain.0})),
            ("amount".into(), json!(amount.to_string())),
            ("enabled".into(), json!(enabled)),
            ("addSecond".into(), json!(add_second)),
        ]);
        prepare_with_context(&plan, &inputs, context.clone(), params)
    };

    let mut cursor = PreparationCursor::new(
        &plan,
        &BTreeMap::from([
            ("domain".into(), json!({"kind":"bytes", "values":domain.0})),
            ("enabled".into(), json!(true)),
            ("addSecond".into(), json!(false)),
        ]),
        &state,
        params,
        ContractAddress::default(),
    )?;
    assert!(matches!(
        cursor.step()?,
        PreparationStep::PendingInputs(missing)
            if missing.len() == 1 && missing[0].name == "amount"
    ));
    cursor.supply_inputs(&BTreeMap::from([("amount".into(), json!("17"))]))?;
    assert!(matches!(cursor.step()?, PreparationStep::Operation { .. }));

    for (amount, enabled, add_second, expected) in [
        (17, true, true, Some(19)),
        (u64::MAX, true, false, Some(u64::MAX)),
        (17, false, true, Some(2)),
        (17, false, false, None),
    ] {
        let execution = prepare(amount, enabled, add_second)?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        let effects = context
            .query(
                &execution.program,
                None,
                &params.cost_model.runtime_cost_model,
            )?
            .context
            .effects;
        assert_eq!(
            effects.shielded_mints.get(&domain).map(|value| *value),
            expected
        );
        assert_eq!(
            effects.unshielded_mints.get(&domain).map(|value| *value),
            expected
        );
        assert_eq!(
            effects.shielded_mints.size(),
            usize::from(expected.is_some())
        );
        assert_eq!(
            effects.unshielded_mints.size(),
            usize::from(expected.is_some())
        );
        assert_eq!(effects.unshielded_inputs.size(), 0);
        assert_eq!(effects.unshielded_outputs.size(), 0);
        assert_eq!(effects.claimed_unshielded_spends.size(), 0);
    }

    let mut forged = prepare(17, true, true)?.preimage;
    let different_amount = prepare(18, true, true)?.preimage;
    forged.public_transcript_inputs = different_amount.public_transcript_inputs.clone();
    assert!(forged.check(&circuit).is_err());
    assert!(prepare(u64::MAX, true, true).is_err());
    Ok(())
}
