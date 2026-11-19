#![cfg(feature = "zkir-321")]

use anyhow::Result;
use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{
    MODULUS, Plan, check,
    control::{InvocationTarget, Session},
    create_state,
    host::{self, Capability, Context, Limits},
    prepare,
    zkir::IrSource,
};
use num_bigint::BigUint;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{collections::BTreeMap, fs, path::PathBuf};

fn artifact_root() -> Result<PathBuf> {
    Ok(std::env::var("NOCTIUM_AGGREGATE_WIRE_ARTIFACTS")?.into())
}

fn bytes(value: &[u8]) -> Json {
    json!({"kind": "bytes", "values": value})
}

fn wire_session(control: &Json, entrypoint: &str, frame: &[u8]) -> Result<Session> {
    let binding_text = control["binding"].as_str().unwrap();
    let pin = hex::encode(Sha256::digest(binding_text.as_bytes()));
    Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([("frame".into(), bytes(frame))]),
        Context {
            protocol_version: 1,
            namespace: "noctium".into(),
            base_revision: "r0".into(),
            attempt_id: "b".repeat(64),
            capabilities: vec![Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "noctium/".into(),
                operations: vec![host::CAS.into()],
            }],
            operations: vec![],
            providers: vec![],
            commit_capability: "commit".into(),
            limits: Limits::default(),
        },
        Some(&pin),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: entrypoint.into(),
        }),
    )
}

#[test]
#[ignore = "requires fresh AggregateSerialization Lean artifacts"]
fn aggregate_wire_matches_compact_reference() -> Result<()> {
    let root = artifact_root()?;
    let name = "AggregateSerialization.Codec.transcode";
    let control: Json = serde_json::from_slice(&fs::read(
        root.join(format!("{name}.witness.control.json")),
    )?)?;
    let plan: Plan = serde_json::from_slice(&fs::read(root.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(root.join(format!("{name}.zkir")))?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let run = |frame: &[u8]| {
        prepare(
            &plan,
            &BTreeMap::from([("frame".into(), bytes(frame))]),
            &state,
            &INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };
    let frame = [44, 1, 1, 0, 1, 1, 12, 42, 200, 255];
    let result = run(&frame)?;
    check(&result, &circuit)?;
    let expected = bytes(&[44, 1, 1, 0, 1, 1, 12, 42, 0, 0]);
    assert_eq!(result.returns_json()["encoding"], expected);
    let host_result = wire_session(&control, "transcode", &frame)?.advance()?;
    assert_eq!(host_result["status"], "completed");
    assert_eq!(host_result["result"], expected);
    for (offset, value) in [(0, 45), (2, 2), (5, 2)] {
        let mut invalid = frame;
        invalid[offset] = value;
        assert!(run(&invalid).is_err(), "invalid byte at offset {offset}");
        assert_eq!(wire_session(&control, "transcode", &invalid)?.advance()?["status"], "failed");
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh AggregateSerialization Lean artifacts"]
fn hosted_and_native_wire_checks_agree() -> Result<()> {
    let root = artifact_root()?;
    let name = "AggregateSerialization.HostedCodec.decode";
    let control: Json = serde_json::from_slice(&fs::read(
        root.join(format!("{name}.witness.control.json")),
    )?)?;
    let binding_text = control["binding"].as_str().unwrap();
    let binding: Json = serde_json::from_str(binding_text)?;
    let open = |frame: &[u8]| wire_session(&control, "decode", frame);
    let mut frame = [0u8; 34];
    frame[0] = 42;
    frame[33] = 91;
    let mut session = open(&frame)?;
    assert_eq!(session.advance()?["status"], "completed");
    let completed = session.private_completion(&binding["nativeRelation"])?;
    let inputs: BTreeMap<String, Json> = serde_json::from_value(completed["inputs"].clone())?;
    let plan: Plan = serde_json::from_slice(&fs::read(root.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(root.join(format!("{name}.zkir")))?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let execution = prepare(
        &plan,
        &inputs,
        &state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )?;
    check(&execution, &circuit)?;
    frame[33] = 0;
    assert_eq!(execution.returns_json()["encoding"], bytes(&frame));

    let modulus: BigUint = MODULUS.parse()?;
    frame[..32].copy_from_slice(&modulus.to_bytes_le());
    let mut invalid = open(&frame)?;
    assert_eq!(invalid.advance()?["status"], "failed");
    Ok(())
}
