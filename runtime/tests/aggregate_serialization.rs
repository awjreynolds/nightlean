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
use transient_crypto::curve::Fr;

fn artifact_root() -> Result<PathBuf> {
    Ok(std::env::var("NOCTIUM_AGGREGATE_WIRE_ARTIFACTS")?.into())
}

fn bytes(value: &[u8]) -> Json {
    json!({"kind": "bytes", "values": value})
}

fn frame_inputs(frame: &[u8]) -> BTreeMap<String, Json> {
    BTreeMap::from([("frame".into(), bytes(frame))])
}

fn wire_session(control: &Json, entrypoint: &str, inputs: BTreeMap<String, Json>) -> Result<Session> {
    let binding_text = control["binding"].as_str().unwrap();
    let pin = hex::encode(Sha256::digest(binding_text.as_bytes()));
    Session::from_json_with_invocation_target(
        control.clone(),
        inputs,
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
            &frame_inputs(frame),
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
    let host_result = wire_session(&control, "transcode", frame_inputs(&frame))?.advance()?;
    assert_eq!(host_result["status"], "completed");
    assert_eq!(host_result["result"], expected);
    for (offset, value) in [(0, 45), (2, 2), (5, 2)] {
        let mut invalid = frame;
        invalid[offset] = value;
        assert!(run(&invalid).is_err(), "invalid byte at offset {offset}");
        assert_eq!(
            wire_session(&control, "transcode", frame_inputs(&invalid))?.advance()?["status"],
            "failed"
        );
    }
    Ok(())
}

#[test]
#[ignore = "requires fresh AggregateSerialization Lean artifacts"]
fn named_payment_return_uses_the_committed_record_layout() -> Result<()> {
    let root = artifact_root()?;
    let name = "AggregateSerialization.Codec.readPayment";
    let control: Json = serde_json::from_slice(&fs::read(
        root.join(format!("{name}.witness.control.json")),
    )?)?;
    let mut plan: Plan = serde_json::from_slice(&fs::read(root.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(root.join(format!("{name}.zkir")))?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let frame = [44, 1, 1, 0, 1, 1, 12, 42, 200, 255];
    let inputs = frame_inputs(&frame);
    let expected = json!({"kind":"struct","id":"Payment","fields":[
        {"name":"info","value":{"kind":"tuple","items":[
            {"kind":"uint","maximum":"300","value":"300"},{"kind":"bool","value":true}
        ]}},
        {"name":"flags","value":{"kind":"vector","items":[
            {"kind":"bool","value":false},{"kind":"bool","value":true}
        ]}},
        {"name":"side","value":{"kind":"enum","id":"Side","variant":"Cancel","fields":[]}},
        {"name":"memo","value":bytes(&[12,42])}
    ]});
    let run = |plan: &Plan, inputs: &BTreeMap<String, Json>| {
        prepare(plan, inputs, &state, &INITIAL_PARAMETERS, ContractAddress::default())
    };
    let mut execution = run(&plan, &inputs)?;
    check(&execution, &circuit)?;
    assert_eq!(execution.returns().len(), 7);
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([("payment".into(), expected.clone())])
    );
    let host_result = wire_session(&control, "readPayment", inputs.clone())?.advance()?;
    assert_eq!(host_result["status"], "completed");
    assert_eq!(host_result["result"], expected);
    for (offset, value) in [(0, 45), (2, 2), (5, 2)] {
        let mut invalid = frame;
        invalid[offset] = value;
        let invalid = frame_inputs(&invalid);
        assert!(run(&plan, &invalid).and_then(|execution| check(&execution, &circuit)).is_err());
        assert_eq!(
            wire_session(&control, "readPayment", invalid)?.advance()?["status"],
            "failed"
        );
    }

    execution.preimage.private_transcript[7] = Fr::from(43u64);
    assert!(check(&execution, &circuit).is_err());
    plan.return_views[0].fields.swap(5, 6);
    assert!(run(&plan, &inputs).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh AggregateSerialization Lean artifacts"]
fn decoded_fields_drive_approval_without_returning_the_record() -> Result<()> {
    let root = artifact_root()?;
    let name = "AggregateSerialization.Codec.authorize";
    let control: Json = serde_json::from_slice(&fs::read(
        root.join(format!("{name}.witness.control.json")),
    )?)?;
    let plan: Plan = serde_json::from_slice(&fs::read(root.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(root.join(format!("{name}.zkir")))?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let run = |frame: &[u8]| {
        prepare(
            &plan,
            &frame_inputs(frame),
            &state,
            &INITIAL_PARAMETERS,
            ContractAddress::default(),
        )
    };
    let frame = [44, 1, 1, 0, 1, 0, 12, 42, 200, 255];
    let mut result = run(&frame)?;
    check(&result, &circuit)?;
    assert_eq!(
        result.returns_json(),
        BTreeMap::from([("approval".into(), json!("42"))])
    );
    let host_result = wire_session(&control, "authorize", frame_inputs(&frame))?.advance()?;
    assert_eq!(host_result["status"], "completed");
    assert_eq!(host_result["result"], "42");
    for (offset, value) in [(2, 0), (4, 0), (5, 1)] {
        let mut denied = frame;
        denied[offset] = value;
        assert!(run(&denied).is_err());
        assert_eq!(
            wire_session(&control, "authorize", frame_inputs(&denied))?.advance()?["status"],
            "failed"
        );
        let before = result.preimage.private_transcript[offset];
        result.preimage.private_transcript[offset] = Fr::from(u64::from(value));
        assert!(check(&result, &circuit).is_err());
        result.preimage.private_transcript[offset] = before;
    }
    result.preimage.private_transcript[7] = Fr::from(43u64);
    assert!(check(&result, &circuit).is_err());
    Ok(())
}

#[test]
#[ignore = "requires fresh AggregateSerialization Lean artifacts"]
fn private_vector_index_is_bounded_and_binds_the_selected_result() -> Result<()> {
    let root = artifact_root()?;
    let name = "AggregateSerialization.Codec.choose";
    let control: Json = serde_json::from_slice(&fs::read(
        root.join(format!("{name}.witness.control.json")),
    )?)?;
    let plan: Plan = serde_json::from_slice(&fs::read(root.join(format!("{name}.impact.json")))?)?;
    let circuit = IrSource::load(fs::File::open(root.join(format!("{name}.zkir")))?)?;
    let state = create_state(&plan, &BTreeMap::new())?;
    let frame = [1, 12, 1, 42, 1, 88];
    let inputs = |position: u64| {
        let mut inputs = frame_inputs(&frame);
        inputs.insert("position".into(), json!(position.to_string()));
        inputs
    };
    let run = |position| {
        prepare(&plan, &inputs(position), &state, &INITIAL_PARAMETERS, ContractAddress::default())
    };
    let host = |position| wire_session(&control, "choose", inputs(position))?.advance();
    for (position, expected) in [(0, "12"), (1, "42"), (2, "88")] {
        let execution = run(position)?;
        check(&execution, &circuit)?;
        assert_eq!(execution.returns_json()["choice"], expected);
        let response = host(position)?;
        assert_eq!(response["status"], "completed");
        assert_eq!(response["result"], expected);
    }
    let mut last = run(2)?;
    assert_eq!(last.preimage.private_transcript, [Fr::from(2u64)]);
    // Position 3 would select the same fallback leaf without the native bound.
    for position in [3, 255] {
        assert!(run(position).and_then(|execution| check(&execution, &circuit)).is_err());
        assert_eq!(host(position)?["status"], "failed");
        last.preimage.private_transcript[0] = Fr::from(position);
        assert!(check(&last, &circuit).is_err());
    }
    last.preimage.private_transcript[0] = Fr::from(1u64);
    assert!(check(&last, &circuit).is_err());
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
    let open = |frame: &[u8]| wire_session(&control, "decode", frame_inputs(frame));
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
