//! Focused checks against freshly compiled event artifacts.
#![cfg(feature = "zkir-321")]

use anyhow::Result;
use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value, ValueAtom};
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use onchain_runtime::{ops::LogEventType, state::StateValue};
use serde_json::json;
use std::{collections::BTreeMap, fs, path::PathBuf};

#[test]
#[ignore = "requires fresh StandardEvents Lean artifacts"]
fn standard_events_bind_payload_order_and_activity() -> Result<()> {
    let output = PathBuf::from(std::env::var("NOCTIUM_EVENT_ARTIFACTS")?);
    let plan: Plan = serde_json::from_slice(&fs::read(
        output.join("StandardEvents.Token.logSpend.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(
        output.join("StandardEvents.Token.logSpend.zkir"),
    )?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let execute = |active: bool, nullifier: &[u8]| {
        prepare(
            &plan,
            &BTreeMap::from([
                ("active".into(), json!(active)),
                (
                    "nullifier".into(),
                    json!({"kind": "bytes", "values": nullifier}),
                ),
            ]),
            &state,
            &INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };
    let nullifier: Vec<u8> = (1..=32).collect();
    let mut active = execute(true, &nullifier)?;
    let inactive = execute(false, &nullifier)?;
    for execution in [&active, &inactive] {
        check(execution, &circuit)?;
        assert!(execution.logs.iter().all(|event| event.version == 1));
        assert_eq!(execution.logs[0].event_type, LogEventType::Paused);
        assert_eq!(
            execution.logs.last().unwrap().event_type,
            LogEventType::Unpaused
        );
    }
    assert_eq!(inactive.logs.len(), 2);
    assert_eq!(active.logs.len(), 3);
    assert_eq!(active.logs[1].event_type, LogEventType::ShieldedSpend);
    let StateValue::Cell(data) = &active.logs[1].data else {
        panic!("expected a byte cell");
    };
    assert_eq!(
        **data,
        AlignedValue {
            value: Value(vec![ValueAtom(nullifier)]),
            alignment: Alignment::singleton(AlignmentAtom::Bytes { length: 32 }),
        }
    );
    active.preimage.public_transcript_inputs = execute(true, &[42; 32])?
        .preimage
        .public_transcript_inputs
        .clone();
    assert!(check(&active, &circuit).is_err());
    Ok(())
}
