use super::*;
use crate::{
    Plan, PreparationCursor, PreparationStep,
    control::AuthenticatedNativeTarget,
    host::{Capability, Context, Limits, Operation, Provider},
    zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::json;
use std::collections::BTreeMap;
use transient_crypto::fab::AlignedValueExt;

const IMPACT: &str = include_str!(
    "../../tests/fixtures/structured-ledger-witness/321/StructuredLedgerWitness.advance.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "../../tests/fixtures/structured-ledger-witness/321/StructuredLedgerWitness.advance.zkir"
);
const WITNESS: &[u8] = include_bytes!(
    "../../tests/fixtures/structured-ledger-witness/321/StructuredLedgerWitness.advance.witness.json"
);
const CONTROL: &[u8] = include_bytes!(
    "../../tests/fixtures/structured-ledger-witness/321/StructuredLedgerWitness.advance.witness.control.json"
);

fn source_inputs(enabled: bool) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("enabled".into(), json!(enabled)),
        ("expected".into(), json!("10")),
    ])
}

fn host_context(attempt_id: &str) -> host::Context {
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "ledger-test-r0".into(),
        attempt_id: attempt_id.into(),
        capabilities: vec![
            Capability {
                id: "derive".into(),
                namespace: "noctium".into(),
                key_prefix: "lookup/".into(),
                operations: vec!["noctium.derive.v1".into()],
            },
            Capability {
                id: "private".into(),
                namespace: "noctium".into(),
                key_prefix: "ledger/".into(),
                operations: vec![host::STAGE.into()],
            },
            Capability {
                id: "commit".into(),
                namespace: "noctium".into(),
                key_prefix: "ledger/".into(),
                operations: vec![host::CAS.into()],
            },
        ],
        operations: vec![Operation {
            operation: "noctium.derive.v1".into(),
            argument_schema: BTreeMap::from([("balance".into(), "Native".into())]),
            result_schema: "Native".into(),
        }],
        providers: vec![Provider {
            input: "derive".into(),
            operation: "noctium.derive.v1".into(),
            capability: "derive".into(),
            arguments: BTreeMap::new(),
        }],
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn artifacts() -> (Json, Json, Json, Json, String) {
    let impact: Json = serde_json::from_str(IMPACT).unwrap();
    let binding_bytes = WITNESS;
    let binding: Json = serde_json::from_slice(binding_bytes).unwrap();
    let control_plan: Json = serde_json::from_slice(CONTROL).unwrap();
    let relation: Json = serde_json::from_slice(CIRCUIT).unwrap();
    let contract = "StructuredLedgerWitness".to_owned();
    control::validate_witness_artifacts(
        &control_plan,
        binding_bytes,
        &relation,
        &impact,
        &contract,
        "advance",
        "StructuredLedgerWitness.advance.zkir",
        crate::profile::NAME,
    )
    .expect("generated witness binding is tied to the selected Impact plan and circuit");
    assert_eq!(binding["target"]["contractName"], contract);
    (impact, control_plan, binding, relation, contract)
}

pub(super) fn source_execution(
    impact: &str,
    circuit_bytes: &[u8],
    control_bytes: &[u8],
    binding_bytes: &[u8],
    source_inputs: BTreeMap<String, Json>,
    initial: &ChargedState<crate::Db>,
    context: host::Context,
) -> (WitnessExecution, Plan, IrSource) {
    let impact_json: Json = serde_json::from_str(impact).unwrap();
    let control_plan: Json = serde_json::from_slice(control_bytes).unwrap();
    let relation: Json = serde_json::from_slice(circuit_bytes).unwrap();
    let entrypoint = impact_json["entrypoint"].as_str().unwrap().to_owned();
    control::validate_witness_artifacts(
        &control_plan,
        binding_bytes,
        &relation,
        &impact_json,
        impact_json["contractName"].as_str().unwrap(),
        &entrypoint,
        impact_json["nativeCircuitFile"].as_str().unwrap(),
        crate::profile::NAME,
    )
    .unwrap();
    let plan: Plan = serde_json::from_str(impact).unwrap();
    let circuit = IrSource::load(circuit_bytes).unwrap();
    let target = AuthenticatedNativeTarget {
        context_id: 1,
        contract_address: "0".repeat(64),
        entrypoint: entrypoint.clone(),
        control_plan,
        control_plan_bytes: control_bytes.to_vec(),
        binding_bytes: binding_bytes.to_vec(),
        relation,
    };
    let mut session = control::Session::from_authenticated_native_target(
        control_bytes,
        source_inputs,
        context,
        target,
    )
    .expect("authenticated source session accepts the emitted artifacts");
    assert!(session.has_ledger_calls());
    let native_inputs = session.partial_native_inputs().unwrap();
    let cursor = PreparationCursor::new(
        &plan,
        &native_inputs.values,
        initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .expect("native cursor uses the same initial state and circuit inputs");
    let execution = WitnessExecution {
        target: None,
        contract_target: None,
        current_state: None,
        session: Some(session),
        ledger: Some(LedgerPreparation::new(cursor, &native_inputs.values)),
        context_id: 1,
        ttl: 0,
        proof_parameters_sha256: String::new(),
        contract_address: "0".repeat(64),
        entrypoint,
    };
    (execution, plan, circuit)
}

fn make_execution(
    enabled: bool,
    attempt_id: &str,
) -> (WitnessExecution, Plan, IrSource, ChargedState<crate::Db>) {
    let plan: Plan = serde_json::from_str(IMPACT).unwrap();
    let initial = crate::create_state(&plan, &BTreeMap::from([("balance".into(), json!("3"))]))
        .expect("initial ledger state is valid");
    let (execution, plan, circuit) = source_execution(
        IMPACT,
        CIRCUIT,
        CONTROL,
        WITNESS,
        source_inputs(enabled),
        &initial,
        host_context(attempt_id),
    );
    (execution, plan, circuit, initial)
}

pub(super) fn advance_native(
    plan: &Plan,
    circuit: &IrSource,
    initial: &ChargedState<crate::Db>,
    inputs: &BTreeMap<String, Json>,
) -> crate::Execution {
    let address = coin_structure::contract::ContractAddress::default();
    let mut cursor = PreparationCursor::new(
        plan,
        inputs,
        initial,
        &ledger::structure::INITIAL_PARAMETERS,
        address,
    )
    .unwrap();
    loop {
        match cursor.step().unwrap() {
            PreparationStep::PendingInputs(missing) => {
                panic!("completed source invocation left native inputs missing: {missing:?}")
            }
            PreparationStep::Operation { .. } => {}
            PreparationStep::Complete => break,
        }
    }
    let execution = cursor.finish().unwrap();
    crate::check(&execution, circuit).expect("native relation accepts source-produced inputs");
    execution
}

fn balance(state: &ChargedState<crate::Db>) -> String {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected contract state array");
    };
    let StateValue::Cell(cell) = &*array.get(0).expect("balance cell exists") else {
        panic!("expected Native balance cell");
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    crate::field_decimal(fields[0])
}

pub(super) fn complete_native_inputs(
    session: &control::Session,
    relation: &Json,
) -> BTreeMap<String, Json> {
    let mut inputs = session.completed_native_inputs(relation).unwrap();
    std::mem::take(&mut inputs.values)
}

#[test]
fn ledger_reads_drive_external_witness_and_later_reads_see_the_write() {
    let attempt_id = "a".repeat(64);
    let (mut execution, plan, circuit, initial) = make_execution(true, &attempt_id);

    let session = execution.session.as_mut().unwrap();
    let _pending = session.advance().unwrap();
    assert!(session.pending_ledger_call().unwrap().is_some());
    let forged: TypedResponse = serde_json::from_value(json!({
        "protocolVersion": 2,
        "requestId": "1",
        "attemptId": attempt_id,
        "outcome": "value",
        "operation": "noctium.ledger.read.v1",
        "capability": "noctium.ledger",
        "schema": "Native",
        "value": "999"
    }))
    .unwrap();
    assert_eq!(
        session.resume_typed(forged).unwrap_err().to_string(),
        "native ledger callback cannot be resumed by a host provider"
    );

    let request = execution.advance().unwrap();
    assert_eq!(request["status"], "need_host");
    assert_eq!(request["request"]["name"], "derive");
    assert_eq!(request["request"]["operation"], "noctium.derive.v1");
    assert_eq!(
        execution.private_request().unwrap()["arguments"]["balance"],
        json!("3"),
        "the provider receives the earlier native ledger read"
    );
    let response: TypedResponse = serde_json::from_value(json!({
        "protocolVersion": 2,
        "requestId": request["request"]["requestId"],
        "attemptId": attempt_id,
        "outcome": "value",
        "operation": "noctium.derive.v1",
        "capability": "derive",
        "schema": "Native",
        "value": "7"
    }))
    .unwrap();
    execution.resume_typed(response).unwrap();
    let result = execution.advance().unwrap();
    assert_eq!(result["status"], "completed");
    assert_eq!(result["result"], json!("10"));

    let session = execution.session.as_mut().unwrap();
    let relation = serde_json::from_slice::<Json>(CIRCUIT).unwrap();
    let host_writes = session.private_completion(&relation).unwrap();
    assert_eq!(
        host_writes["hostWrites"]["ledger/last"]["value"],
        json!("7")
    );
    let inputs = complete_native_inputs(session, &relation);
    let native = advance_native(&plan, &circuit, &initial, &inputs);
    assert_eq!(balance(&native.after.state), "10");
    assert_eq!(
        native.returns_json(),
        BTreeMap::from([("result".into(), json!("10"))])
    );
}

#[test]
fn inactive_ledger_witness_branch_skips_the_external_provider() {
    let attempt_id = "b".repeat(64);
    let (mut execution, plan, circuit, initial) = make_execution(false, &attempt_id);
    let result = execution.advance().unwrap();
    assert_eq!(result["status"], "completed");
    assert_eq!(result["result"], json!("0"));

    let session = execution.session.as_mut().unwrap();
    let relation = serde_json::from_slice::<Json>(CIRCUIT).unwrap();
    let inputs = complete_native_inputs(session, &relation);
    let native = advance_native(&plan, &circuit, &initial, &inputs);
    assert_eq!(balance(&native.after.state), "3");
    assert_eq!(
        native.returns_json(),
        BTreeMap::from([("result".into(), json!("0"))])
    );
}

#[test]
fn failed_external_witness_does_not_stage_private_state() {
    let attempt_id = "c".repeat(64);
    let (mut execution, _plan, _circuit, _initial) = make_execution(true, &attempt_id);
    let request = execution.advance().unwrap();
    let response: TypedResponse = serde_json::from_value(json!({
        "protocolVersion": 2,
        "requestId": request["request"]["requestId"],
        "attemptId": attempt_id,
        "outcome": "value",
        "operation": request["request"]["operation"],
        "capability": request["request"]["capability"],
        "schema": request["request"]["schema"],
        "value": "8"
    }))
    .unwrap();
    execution.resume_typed(response).unwrap();
    assert_eq!(execution.advance().unwrap()["status"], "failed");
}

#[test]
fn ledger_callback_metadata_rejects_a_different_native_read() {
    let (impact, mut control_plan, mut binding, relation, contract) = artifacts();
    binding["ledgerCalls"][0]["read"] = binding["ledgerCalls"][2]["read"].clone();
    let binding_text = serde_json::to_string(&binding).unwrap() + "\n";
    control_plan["binding"] = json!(binding_text);
    assert!(
        control::validate_witness_artifacts(
            &control_plan,
            binding_text.as_bytes(),
            &relation,
            &impact,
            &contract,
            "advance",
            "StructuredLedgerWitness.advance.zkir",
            crate::profile::NAME,
        )
        .is_err()
    );
}
