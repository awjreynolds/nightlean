#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::{
    coin::{PublicAddress, ShieldedTokenType, TokenType, UnshieldedTokenType, UserAddress},
    contract::ContractAddress,
};
use noctium_runtime::{Plan, check, create_state, prepare_with_context, zkir::IrSource};
use onchain_runtime::context::QueryContext;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};

fn fresh_artifacts() -> (Plan, IrSource) {
    let directory = PathBuf::from(
        std::env::var_os("NOCTIUM_KERNEL_CONTEXT_DIR")
            .expect("set NOCTIUM_KERNEL_CONTEXT_DIR to the fresh Lean emission directory"),
    );
    let plan: Plan = serde_json::from_slice(
        &fs::read(directory.join("NativeKernelContext.inspect.impact.json"))
            .expect("fresh kernel context Impact plan exists"),
    )
    .expect("kernel context Impact plan parses");
    let circuit = IrSource::load(
        fs::File::open(directory.join("NativeKernelContext.inspect.zkir"))
            .expect("fresh kernel context ZKIR exists"),
    )
    .expect("kernel context ZKIR parses");
    (plan, circuit)
}

fn bytes(value: &[u8; 32]) -> Json {
    json!({"kind":"bytes", "values":value})
}

#[test]
#[ignore = "requires fresh NativeKernelContext artifacts in NOCTIUM_KERNEL_CONTEXT_DIR"]
fn combined_kernel_context_matches_checked_native_relation() -> anyhow::Result<()> {
    let (plan, circuit) = fresh_artifacts();
    for operation in ["readContractAddress", "readCaller", "readTokenBalance"] {
        assert!(
            plan.operations.iter().any(|instruction| match instruction {
                noctium_runtime::Instruction::Guarded {
                    operation: nested, ..
                } => match operation {
                    "readContractAddress" => matches!(
                        nested.as_ref(),
                        noctium_runtime::Instruction::ReadContractAddress { .. }
                    ),
                    "readCaller" => matches!(
                        nested.as_ref(),
                        noctium_runtime::Instruction::ReadCaller { .. }
                    ),
                    "readTokenBalance" => matches!(
                        nested.as_ref(),
                        noctium_runtime::Instruction::ReadTokenBalance { .. }
                    ),
                    _ => false,
                },
                _ => false,
            }),
            "the combined plan includes guarded {operation}"
        );
    }

    let empty = create_state(&plan, &BTreeMap::new())?;
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let self_address = ContractAddress(HashOutput(std::array::from_fn(|index| index as u8)));
    let caller_bytes = std::array::from_fn(|index| (index + 41) as u8);
    let caller_contract = PublicAddress::Contract(ContractAddress(HashOutput(caller_bytes)));
    let caller_user = PublicAddress::User(UserAddress(HashOutput(caller_bytes)));
    let color = HashOutput(std::array::from_fn(|index| (index + 1) as u8));

    let execute = |enabled, caller, is_unshielded| -> anyhow::Result<_> {
        let mut context = QueryContext::new(empty.clone(), self_address);
        context.call_context.caller = caller;
        context.call_context.balance = context
            .call_context
            .balance
            .insert(TokenType::Unshielded(UnshieldedTokenType(color)), 17);
        context.call_context.balance = context
            .call_context
            .balance
            .insert(TokenType::Shielded(ShieldedTokenType(color)), 23);
        let inputs = BTreeMap::from([
            ("enabled".into(), json!(enabled)),
            ("color".into(), bytes(&color.0)),
            ("isUnshielded".into(), json!(is_unshielded)),
        ]);
        let execution = prepare_with_context(&plan, &inputs, context, params)?;
        assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
        Ok(execution)
    };

    let address_json = |value: &[u8; 32]| bytes(value);
    let zero = [0; 32];
    let cases = [
        (
            true,
            Some(caller_contract),
            true,
            [true, true, false, false],
            self_address.0.0,
            17u128,
        ),
        (
            true,
            Some(caller_user),
            false,
            [true, false, true, true],
            self_address.0.0,
            23u128,
        ),
        (
            true,
            None,
            true,
            [false, false, false, false],
            self_address.0.0,
            17u128,
        ),
        (
            false,
            Some(caller_contract),
            true,
            [false, false, false, false],
            zero,
            0u128,
        ),
    ];

    for (enabled, caller, is_unshielded, [has_caller, is_contract, is_user, _], own, balance) in
        cases
    {
        let execution = execute(enabled, caller, is_unshielded)?;
        let returns = execution.returns_json();
        let caller_address = if has_caller { caller_bytes } else { zero };
        assert_eq!(returns["selfAddress"], address_json(&own));
        assert_eq!(returns["hasCaller"], json!(has_caller));
        assert_eq!(returns["contractCaller"], json!(is_contract));
        assert_eq!(
            returns["callerContract"],
            address_json(if is_contract { &caller_address } else { &zero })
        );
        assert_eq!(
            returns["callerUser"],
            address_json(if is_user { &caller_address } else { &zero })
        );
        assert_eq!(returns["tokenBalance"], json!(balance.to_string()));
        assert_eq!(execution.after.state, empty);
    }

    Ok(())
}
