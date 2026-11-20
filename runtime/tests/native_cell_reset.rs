#![cfg(feature = "zkir-321")]

use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, fs, path::PathBuf};

fn state_values(amount: &str, nonce: &str, active: bool, memo: &[u8]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("amount".into(), json!(amount)),
        ("nonce".into(), json!(nonce)),
        ("active".into(), json!(active)),
        ("memo".into(), json!({"kind": "bytes", "values": memo})),
    ])
}

#[test]
#[ignore = "requires fresh Lean output via NOCTIUM_CELL_RESET_DIR"]
fn guarded_cell_reset_checks_and_matches_the_native_ledger_state() {
    let artifacts = PathBuf::from(std::env::var_os("NOCTIUM_CELL_RESET_DIR").unwrap());
    let plan_bytes = fs::read(artifacts.join("NativeCellReset.clear.impact.json")).unwrap();
    let circuit_bytes = fs::read(artifacts.join("NativeCellReset.clear.zkir")).unwrap();
    let plan: Plan = serde_json::from_slice(&plan_bytes).unwrap();
    let circuit = IrSource::load(circuit_bytes.as_slice()).unwrap();
    let initial = create_state(
        &plan,
        &state_values("42", "17", true, &[115, 101, 101, 100]),
    )
    .unwrap();
    let reset = create_state(&plan, &state_values("0", "0", false, &[0; 4])).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    for enabled in [true, false] {
        let execution = prepare(
            &plan,
            &BTreeMap::from([("enabled".into(), json!(enabled))]),
            &initial,
            params,
            address,
        )
        .unwrap();
        check(&execution, &circuit).unwrap();

        let expected = if enabled { &reset } else { &initial };
        assert_eq!(execution.after.state.get_ref(), expected.get_ref());
        let memo = if enabled {
            [0; 4]
        } else {
            [115, 101, 101, 100]
        };
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([
                (
                    "amountAfter".into(),
                    json!(if enabled { "0" } else { "42" })
                ),
                ("nonceAfter".into(), json!(if enabled { "0" } else { "17" })),
                ("activeAfter".into(), json!(!enabled)),
                ("memoAfter".into(), json!({"kind": "bytes", "values": memo}),),
            ])
        );
    }
}
