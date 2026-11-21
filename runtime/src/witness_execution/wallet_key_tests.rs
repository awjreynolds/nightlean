use super::ledger_tests::{advance_native, complete_native_inputs};
use super::*;
use crate::zkir::IrSource;
use crate::Plan;
use host::{Capability, Context, Limits, Operation, Provider};
use serde_json::{json, Value as Json};
use std::collections::BTreeMap;

const ARTIFACT_STEM: &str = "OwnPublicKeyWitnessFixture.OwnPublicKeyWitness.capture";

const PROVIDER_NAME: &str = "OwnPublicKeyWitnessFixture.ownPublicKey";
const OPERATION: &str = "noctium.witness.OwnPublicKeyWitnessFixture.ownPublicKey.v1";
const CAPABILITY: &str = "OwnPublicKeyWitnessFixture.ownPublicKey";
const RESULT_SCHEMA: &str = "Aggregate:t0";

fn host_context(attempt_id: &str) -> Context {
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "wallet-key-r0".into(),
        attempt_id: attempt_id.into(),
        capabilities: vec![
            Capability {
                id: CAPABILITY.into(),
                namespace: "noctium".into(),
                key_prefix: "wallet/".into(),
                operations: vec![OPERATION.into()],
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
            operation: OPERATION.into(),
            argument_schema: BTreeMap::new(),
            result_schema: RESULT_SCHEMA.into(),
        }],
        providers: vec![Provider {
            input: PROVIDER_NAME.into(),
            operation: OPERATION.into(),
            capability: CAPABILITY.into(),
            arguments: BTreeMap::new(),
        }],
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn state(plan: &Plan, public_key: &[u8; 32]) -> onchain_runtime::state::ChargedState<crate::Db> {
    crate::create_state(
        plan,
        &BTreeMap::from([(
            "registeredKey".into(),
            json!({"kind":"bytes", "values":public_key}),
        )]),
    )
    .unwrap()
}

fn reply(request: &Json, attempt_id: &str, value: Json) -> crate::control::TypedResponse {
    serde_json::from_value(json!({
        "protocolVersion":2,
        "requestId":request["request"]["requestId"],
        "attemptId":attempt_id,
        "outcome":"value",
        "operation":request["request"]["operation"],
        "capability":request["request"]["capability"],
        "schema":request["request"]["schema"],
        "value":value
    }))
    .unwrap()
}

fn public_key_value(id: &str, bytes: &[u8]) -> Json {
    json!({
        "kind":"struct",
        "id":id,
        "fields":[{"name":"bytes", "value":{"kind":"bytes", "values":bytes}}]
    })
}

fn wallet_execution(
    impact: &str,
    circuit_bytes: &[u8],
    control_bytes: &[u8],
    binding_bytes: &[u8],
    context: Context,
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
    let target = crate::control::AuthenticatedNativeTarget {
        context_id: 1,
        contract_address: "0".repeat(64),
        entrypoint: entrypoint.clone(),
        control_plan,
        control_plan_bytes: control_bytes.to_vec(),
        binding_bytes: binding_bytes.to_vec(),
        relation,
    };
    let session = control::Session::from_authenticated_native_target(
        control_bytes,
        BTreeMap::new(),
        context,
        target,
    )
    .expect("authenticated native source artifacts open a witness session");
    assert!(!session.has_ledger_calls());
    let execution = WitnessExecution {
        target: None,
        contract_target: None,
        current_state: None,
        session: Some(session),
        ledger: None,
        context_id: 1,
        ttl: 0,
        proof_parameters_sha256: String::new(),
        contract_address: "0".repeat(64),
        entrypoint,
    };
    (execution, plan, circuit)
}

#[test]
#[ignore = "requires fresh 3.2.1 artifacts via NOCTIUM_WALLET_KEY_ARTIFACTS"]
fn named_wallet_key_witness_returns_nominal_bytes_and_rejects_wrong_shapes() {
    let artifacts = std::path::PathBuf::from(
        std::env::var_os("NOCTIUM_WALLET_KEY_ARTIFACTS")
            .expect("set NOCTIUM_WALLET_KEY_ARTIFACTS to the emitted artifacts directory"),
    );
    let read = |extension: &str| {
        std::fs::read(artifacts.join(format!("{ARTIFACT_STEM}.{extension}"))).unwrap()
    };
    let impact = String::from_utf8(read("impact.json")).unwrap();
    let circuit_bytes = read("zkir");
    let binding = read("witness.json");
    let control = read("witness.control.json");
    let attempt_id = "b".repeat(64);
    let key = std::array::from_fn(|index| index as u8 + 1);
    let zero = [0; 32];
    let plan: Plan = serde_json::from_str(&impact).unwrap();
    let initial = state(&plan, &zero);
    let expected = state(&plan, &key);
    let (mut execution, plan, circuit) = wallet_execution(
        &impact,
        &circuit_bytes,
        &control,
        &binding,
        host_context(&attempt_id),
    );

    let request = execution.advance().unwrap();
    assert_eq!(request["status"], "need_host");
    assert_eq!(request["request"]["name"], PROVIDER_NAME);
    assert_eq!(request["request"]["operation"], OPERATION);
    assert_eq!(request["request"]["capability"], CAPABILITY);
    assert_eq!(request["request"]["schema"], RESULT_SCHEMA);
    assert_eq!(execution.private_request().unwrap()["arguments"], json!({}));

    let malformed = public_key_value("Noctium.Midnight.ZswapCoinPublicKey", &key[..31]);
    assert!(execution
        .resume_typed(reply(&request, &attempt_id, malformed))
        .is_err());
    let wrong_identity = public_key_value("Noctium.Midnight.OtherPublicKey", &key);
    assert!(execution
        .resume_typed(reply(&request, &attempt_id, wrong_identity))
        .is_err());

    let wallet_key = public_key_value("Noctium.Midnight.ZswapCoinPublicKey", &key);
    execution
        .resume_typed(reply(&request, &attempt_id, wallet_key))
        .expect("the exact nominal Bytes32 provider result is accepted");
    assert_eq!(execution.advance().unwrap()["status"], "completed");

    let session = execution.session.as_mut().unwrap();
    let relation: Json = serde_json::from_slice(&circuit_bytes).unwrap();
    let inputs = complete_native_inputs(session, &relation);
    let native = advance_native(&plan, &circuit, &initial, &inputs);
    assert_eq!(native.after.state, expected);
}
