#![cfg(feature = "zkir-321")]

use base_crypto::{fab::AlignedValue, hash::HashOutput};
use coin_structure::{
    coin::{ShieldedTokenType, TokenType, UnshieldedTokenType},
    contract::ContractAddress,
};
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::{context::QueryContext, state::StateValue};
use serde_json::json;
use std::{collections::BTreeMap, fs, path::PathBuf};

#[test]
#[ignore = "requires generated NativeTokenBalance artifacts in NOCTIUM_BALANCE_DIR"]
fn tagged_token_balance_reads_bind_to_the_selected_ledger_namespace() -> anyhow::Result<()> {
    let directory =
        PathBuf::from(std::env::var_os("NOCTIUM_BALANCE_DIR").expect("NOCTIUM_BALANCE_DIR"));
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join("NativeTokenBalance.inspect.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        directory.join("NativeTokenBalance.inspect.zkir"),
    )?)?;
    let initial = create_state(&plan, &BTreeMap::from([("recorded".into(), json!("17"))]))?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let color = HashOutput(std::array::from_fn(|index| (index + 1) as u8));
    let context = |unshielded: Option<u128>, shielded: Option<u128>| {
        let mut context = QueryContext::new(initial.clone(), ContractAddress::default());
        let balances = &mut context.call_context.balance;
        if let Some(amount) = unshielded {
            *balances = balances.insert(TokenType::Unshielded(UnshieldedTokenType(color)), amount);
        }
        if let Some(amount) = shielded {
            *balances = balances.insert(TokenType::Shielded(ShieldedTokenType(color)), amount);
        }
        context
    };
    let prepare = |is_unshielded, limit: u128, enabled, read_exact, unshielded, shielded| {
        let inputs = BTreeMap::from([
            ("color".into(), json!({"kind":"bytes", "values":color.0})),
            ("isUnshielded".into(), json!(is_unshielded)),
            ("limit".into(), json!(limit.to_string())),
            ("enabled".into(), json!(enabled)),
            ("readExact".into(), json!(read_exact)),
        ]);
        prepare_with_context(&plan, &inputs, context(unshielded, shielded), params)
    };
    let execute = |is_unshielded, limit, enabled, read_exact, unshielded, shielded| {
        let execution = prepare(
            is_unshielded,
            limit,
            enabled,
            read_exact,
            unshielded,
            shielded,
        )?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        Ok::<_, anyhow::Error>(execution)
    };

    for (tag, expected, below, above) in [(true, 17u128, true, false), (false, 23u128, false, true)]
    {
        let execution = execute(tag, 20, true, true, Some(17), Some(23))?;
        let returns = execution.returns_json();
        assert_eq!(returns["exactAmount"], json!(expected.to_string()));
        assert_eq!(returns["belowLimit"], json!(below));
        assert_eq!(returns["aboveLimit"], json!(above));
        let StateValue::Array(state) = execution.after.state.get_ref() else {
            panic!("expected contract state array");
        };
        let StateValue::Cell(recorded) = state.get(0).unwrap() else {
            panic!("expected recorded balance cell");
        };
        assert_eq!(**recorded, AlignedValue::from(expected));
    }

    let absent = execute(true, 20, true, true, None, Some(23))?;
    assert_eq!(absent.returns_json()["exactAmount"], json!("0"));
    assert_eq!(absent.returns_json()["belowLimit"], json!(true));
    assert_eq!(absent.returns_json()["aboveLimit"], json!(false));

    let wide_exact = execute(false, u128::MAX, false, true, None, Some(u128::MAX))?;
    assert_eq!(
        wide_exact.returns_json()["exactAmount"],
        json!(u128::MAX.to_string())
    );
    assert!(prepare(false, 0, true, false, None, Some(u128::MAX)).is_err());
    assert!(prepare(false, u128::MAX, true, false, None, Some(0)).is_err());

    let inactive = execute(true, 20, false, false, Some(17), Some(23))?;
    assert_eq!(inactive.returns_json()["exactAmount"], json!("0"));
    assert_eq!(inactive.returns_json()["belowLimit"], json!(false));
    assert_eq!(inactive.returns_json()["aboveLimit"], json!(false));

    let predicate_only = execute(true, 10, true, false, Some(8), Some(23))?;
    let cost = &params.cost_model.runtime_cost_model;
    assert!(
        context(Some(9), Some(23))
            .query(&predicate_only.program, None, cost)
            .is_ok()
    );
    assert!(
        context(Some(10), Some(23))
            .query(&predicate_only.program, None, cost)
            .is_err()
    );
    Ok(())
}
