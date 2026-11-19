//! Public Rust ownership path. The ignored end-to-end test uses the same functional bundle and
//! SRS as the native client qualification, while compiling against public crate APIs only.
use futures::executor::block_on;
use noctium_runtime::{
    artifacts::{self, Role, VerifiedBundle},
    control::TypedResponse,
    host::{self, Capability, Context, Limits, Operation, Provider},
    profile,
    proof::{self, ProofRequest, ProofService, ServiceError, TrustedParameters, WitnessTarget},
    witness_execution::{Error, WitnessExecution},
};
use rand::rngs::OsRng;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    future,
    sync::atomic::{AtomicUsize, Ordering},
};

#[allow(dead_code)]
#[path = "fixtures/private-authoring/321/bindings/rust/NoctiumExamples.PrivateStateCounter.advance.rs"]
mod generated_counter;

#[test]
fn generated_rust_binding_encodes_inputs_and_correlates_provider_replies() {
    let inputs = generated_counter::Inputs { arg_expected: 7 }.into_source_inputs();
    assert_eq!(inputs, BTreeMap::from([("expected".into(), json!("7"))]));
    let mut request = json!({
        "requestId": "42",
        "name": "NoctiumExamples.nextValue",
        "operation": "noctium.witness.NoctiumExamples.nextValue.v1",
        "capability": "NoctiumExamples.nextValue",
        "schema": "UIntRange<256>"
    });
    let reply = generated_counter::reply_NoctiumExamples_dnextValue(&request, "attempt", 7).unwrap();
    assert_eq!(reply.request_id, "42");
    assert_eq!(reply.value, Some(json!("7")));
    request["schema"] = json!("Bool");
    assert!(matches!(
        generated_counter::reply_NoctiumExamples_dnextValue(&request, "attempt", 7),
        Err(Error::InvalidSource)
    ));
}

const TTL: u64 = 2_000_000_000;

fn required_env(name: &str) -> String {
    std::env::var(name).unwrap_or_else(|_| panic!("missing {name}"))
}

fn fixture() -> (VerifiedBundle, TrustedParameters) {
    let root = required_env("NOCTIUM_WITNESS_PUBLIC_BUNDLE");
    let manifest = required_env("NOCTIUM_WITNESS_PUBLIC_MANIFEST_SHA256");
    let bundle = artifacts::verify(root.as_ref(), Some(&manifest)).unwrap();
    let bytes = std::fs::read(required_env("NOCTIUM_WITNESS_PUBLIC_PARAMETERS")).unwrap();
    let digest = required_env("NOCTIUM_WITNESS_PUBLIC_PARAMETERS_SHA256");
    let parameters = TrustedParameters::from_bytes(&bytes, 7, &digest).unwrap();
    (bundle, parameters)
}

fn same_degree_alternate_parameters(source: &[u8]) -> Vec<u8> {
    const POINT_BYTES: usize = 96;
    const G2_BYTES: usize = 384;
    let old_k = 8usize;
    let new_k = 7usize;
    assert_eq!(source.len(), 4 + (1 << old_k) * 2 * POINT_BYTES + G2_BYTES);
    assert_eq!(
        u32::from_le_bytes(source[..4].try_into().unwrap()),
        old_k as u32
    );
    let old_count = 1 << old_k;
    let new_count = 1 << new_k;
    let first_start = 4;
    let second_start = first_start + old_count * POINT_BYTES;
    let g2_start = second_start + old_count * POINT_BYTES;
    let mut alternate = Vec::with_capacity(4 + new_count * 2 * POINT_BYTES + G2_BYTES);
    alternate.extend_from_slice(&(new_k as u32).to_le_bytes());
    alternate.extend_from_slice(&source[first_start..first_start + new_count * POINT_BYTES]);
    alternate.extend_from_slice(&source[second_start..second_start + new_count * POINT_BYTES]);
    alternate.extend_from_slice(&source[g2_start..]);
    alternate
}

fn alternate_parameters() -> TrustedParameters {
    let source = std::fs::read(required_env("NOCTIUM_WITNESS_PUBLIC_ALT_PARAMETERS")).unwrap();
    let bytes = same_degree_alternate_parameters(&source);
    let digest = hex::encode(Sha256::digest(&bytes));
    TrustedParameters::from_bytes(&bytes, 7, &digest).unwrap()
}

fn source_context(plan: &Json, attempt_id: &str) -> Context {
    let mut operations = BTreeMap::<String, Operation>::new();
    let mut providers = Vec::new();
    let mut capability_map = BTreeMap::<String, (String, BTreeSet<String>)>::new();
    for signature in plan["witnesses"].as_array().unwrap() {
        let name = signature["name"].as_str().unwrap().to_owned();
        let operation = signature["operation"].as_str().unwrap().to_owned();
        let capability = signature["capability"].as_str().unwrap().to_owned();
        let private_key = signature["privateKey"].as_str().map(str::to_owned);
        let parameters = signature["parameters"].as_array().unwrap();
        let mut argument_schema = parameters
            .iter()
            .map(|parameter| {
                (
                    parameter["name"].as_str().unwrap().to_owned(),
                    parameter["type"].as_str().unwrap().to_owned(),
                )
            })
            .collect::<BTreeMap<_, _>>();
        if operation == host::READ {
            argument_schema.insert("key".into(), "Key".into());
        }
        operations.insert(
            operation.clone(),
            Operation {
                operation: operation.clone(),
                argument_schema,
                result_schema: signature["resultType"].as_str().unwrap().to_owned(),
            },
        );
        let prefix = private_key
            .as_deref()
            .map(|key| {
                key.rsplit_once('/')
                    .map(|(root, _)| format!("{root}/"))
                    .unwrap_or_else(|| key.to_owned())
            })
            .unwrap_or_else(|| "lookup/".into());
        let entry = capability_map
            .entry(capability.clone())
            .or_insert_with(|| (prefix.clone(), BTreeSet::new()));
        assert_eq!(entry.0, prefix);
        entry.1.insert(operation.clone());
        if private_key.is_some() {
            entry.1.insert(host::STAGE.into());
        }
        providers.push(Provider {
            input: name,
            operation,
            capability,
            arguments: private_key
                .map(|key| BTreeMap::from([("key".into(), json!(key))]))
                .unwrap_or_default(),
        });
    }
    let private = capability_map
        .entry("private".into())
        .or_insert_with(|| ("cache/".into(), BTreeSet::new()));
    private.1.insert(host::STAGE.into());
    let mut capabilities = capability_map
        .into_iter()
        .map(|(id, (key_prefix, operations))| Capability {
            id,
            namespace: "noctium".into(),
            key_prefix,
            operations: operations.into_iter().collect(),
        })
        .collect::<Vec<_>>();
    capabilities.push(Capability {
        id: "commit".into(),
        namespace: "noctium".into(),
        key_prefix: "cache/".into(),
        operations: vec![host::CAS.into()],
    });
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "preview-r0".into(),
        attempt_id: attempt_id.into(),
        capabilities,
        operations: operations.into_values().collect(),
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn inputs(expected: &str) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("expected".into(), json!(expected)),
        ("seed".into(), json!("7")),
    ])
}

fn complete_source(execution: &mut WitnessExecution, attempt_id: &str) -> bool {
    for _ in 0..64 {
        let status = execution.advance().unwrap();
        match status["status"].as_str().unwrap() {
            "completed" => return true,
            "failed" => return false,
            "need_host" => {
                let request = &status["request"];
                let value = match request["name"].as_str().unwrap() {
                    "cache" => json!("1"),
                    "lookup" => json!("14"),
                    other => panic!("unexpected provider {other}"),
                };
                let response: TypedResponse = serde_json::from_value(json!({
                    "protocolVersion": 2,
                    "requestId": request["requestId"],
                    "attemptId": attempt_id,
                    "outcome": "value",
                    "operation": request["operation"],
                    "capability": request["capability"],
                    "schema": request["schema"],
                    "value": value,
                }))
                .unwrap();
                execution.resume_typed(response).unwrap();
            }
            other => panic!("unexpected source status {other}"),
        }
    }
    panic!("source witness exceeded the request bound")
}

fn source_inputs_and_context(
    plan: &Json,
    expected: &str,
    attempt: &str,
) -> (BTreeMap<String, Json>, Context) {
    (inputs(expected), source_context(plan, attempt))
}

fn descriptor() -> Json {
    json!({
        "abiVersion": 1,
        "policy": {
            "networkId": "noctium-test",
            "genesis": "8".repeat(64),
            "specVersion": 2001100,
            "transactionVersion": 4,
            "profile": profile::NAME,
            "maxDust": "10000000000000000000000"
        },
        "capabilities": {
            "chain": "chain",
            "funding": "wallet",
            "signing": "signer",
            "journal": "store"
        }
    })
}

fn deployment_context(attempt_id: &str) -> Context {
    Context {
        protocol_version: 1,
        namespace: "noctium-deploy".into(),
        base_revision: "deployment-r0".into(),
        attempt_id: attempt_id.into(),
        capabilities: vec![Capability {
            id: "commit".into(),
            namespace: "noctium-deploy".into(),
            key_prefix: "deploy/".into(),
            operations: vec![host::CAS.into()],
        }],
        operations: Vec::new(),
        providers: Vec::new(),
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

struct CountingLocalProver {
    calls: AtomicUsize,
}
impl ProofService for CountingLocalProver {
    async fn prove(&self, request: ProofRequest<'_>) -> std::result::Result<Vec<u8>, ServiceError> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        request.prove_locally(OsRng).await
    }
}

struct PendingProofService;
impl ProofService for PendingProofService {
    async fn prove(
        &self,
        _request: ProofRequest<'_>,
    ) -> std::result::Result<Vec<u8>, ServiceError> {
        future::pending().await
    }
}

#[test]
#[ignore = "requires the authenticated functional source bundle and pinned public SRS fixtures"]
fn public_rust_api_owns_source_inputs_runtime_proof_and_client_handoff() {
    let (bundle, parameters) = fixture();
    let alternate = alternate_parameters();
    assert_eq!(alternate.k(), parameters.k());
    assert_ne!(alternate.sha256(), parameters.sha256());
    let control_plan: Json =
        serde_json::from_slice(bundle.file(Role::WitnessControl).unwrap()).unwrap();
    let state = br#"{"state":{"total":"0"}}"#;
    let attempt = "a".repeat(64);
    let mut rng = OsRng;

    // The same target rejects an independently identified, same-degree parameter set.
    let mismatched_target =
        WitnessTarget::from_state_config(&bundle, state, &parameters, TTL, &mut rng).unwrap();
    let (bad_inputs, bad_context) = source_inputs_and_context(&control_plan, "14", &attempt);
    assert!(matches!(
        WitnessExecution::from_target(
            &bundle,
            mismatched_target,
            bad_inputs,
            bad_context,
            &alternate,
            TTL,
        ),
        Err(Error::Proof(proof::Error::BindingMismatch))
    ));

    // A different source invocation over the same sidecar fails its source assertion.
    let wrong_target =
        WitnessTarget::from_state_config(&bundle, state, &parameters, TTL, &mut rng).unwrap();
    let (wrong_inputs, wrong_context) =
        source_inputs_and_context(&control_plan, "15", &"b".repeat(64));
    let mut wrong = WitnessExecution::from_target(
        &bundle,
        wrong_target,
        wrong_inputs,
        wrong_context,
        &parameters,
        TTL,
    )
    .unwrap();
    assert!(!complete_source(&mut wrong, &"b".repeat(64)));
    assert!(matches!(
        wrong.prepare_proof(&bundle, TTL, &mut rng),
        Err(Error::InvalidSource)
    ));

    let cancelled_target =
        WitnessTarget::from_state_config(&bundle, state, &parameters, TTL, &mut rng).unwrap();
    let (cancelled_inputs, cancelled_context) =
        source_inputs_and_context(&control_plan, "14", &"c".repeat(64));
    let mut cancelled = WitnessExecution::from_target(
        &bundle,
        cancelled_target,
        cancelled_inputs,
        cancelled_context,
        &parameters,
        TTL,
    )
    .unwrap();
    assert_eq!(cancelled.cancel().unwrap()["status"], "cancelled");
    assert!(matches!(cancelled.advance(), Err(Error::State)));
    assert!(matches!(
        cancelled.prepare_proof(&bundle, TTL, &mut rng),
        Err(Error::State)
    ));

    let target =
        WitnessTarget::from_state_config(&bundle, state, &parameters, TTL, &mut rng).unwrap();
    let address = target.contract_address().to_owned();
    let (source_inputs, context) = source_inputs_and_context(&control_plan, "14", &attempt);
    let mut execution =
        WitnessExecution::from_target(&bundle, target, source_inputs, context, &parameters, TTL)
            .unwrap();
    assert_eq!(execution.contract_address(), address);
    assert_eq!(execution.entrypoint(), "claim");
    assert!(complete_source(&mut execution, &attempt));

    // Failed preflight keeps the completed source invocation available for a corrected retry.
    assert!(matches!(
        execution.prepare_proof(&bundle, TTL + 1, &mut rng),
        Err(Error::Proof(proof::Error::BindingMismatch))
    ));
    let mut proof = execution.prepare_proof(&bundle, TTL, &mut rng).unwrap();

    // A same-k SRS mismatch rejects before the proof service sees private witness material.
    let service = CountingLocalProver {
        calls: AtomicUsize::new(0),
    };
    assert!(matches!(
        block_on(proof.prove(&service, &alternate, 1_048_576, future::pending())),
        Err(Error::Proof(proof::Error::InvalidParameters))
    ));
    assert_eq!(service.calls.load(Ordering::SeqCst), 0);

    let mut proved =
        block_on(proof.prove(&service, &parameters, 1_048_576, future::pending())).unwrap();
    assert_eq!(service.calls.load(Ordering::SeqCst), 1);
    assert!(matches!(
        block_on(proof.prove(&service, &parameters, 1_048_576, future::pending())),
        Err(Error::State)
    ));
    assert_eq!(service.calls.load(Ordering::SeqCst), 1);

    let descriptor = serde_json::to_vec(&descriptor()).unwrap();
    assert!(proved.start_call_client(b"{}").is_err());
    let deploy_context = deployment_context(&"c".repeat(64));
    let setup = serde_json::to_vec(&json!({"hostContext":deploy_context,"stages":[]})).unwrap();
    let mut deploy_client = proved.start_deployment_client(&descriptor, &setup).unwrap();
    assert!(deploy_client.status().is_object());
    assert!(proved.start_deployment_client(&descriptor, &setup).is_err());
    let mut call_client = proved.start_call_client(&descriptor).unwrap();
    assert!(call_client.status().is_object());
    assert!(proved.start_call_client(&descriptor).is_err());
    assert!(call_client.detachable());
    let _ = (&mut deploy_client, &mut call_client);

    // A completed source handoff is terminal after either explicit cancellation or a dropped
    // proof future that was polled. In both cases its private Runtime is discarded.
    let cancel_target =
        WitnessTarget::from_state_config(&bundle, state, &parameters, TTL, &mut rng).unwrap();
    let (cancel_inputs, cancel_context) =
        source_inputs_and_context(&control_plan, "14", &"d".repeat(64));
    let mut cancel_execution = WitnessExecution::from_target(
        &bundle,
        cancel_target,
        cancel_inputs,
        cancel_context,
        &parameters,
        TTL,
    )
    .unwrap();
    assert!(complete_source(&mut cancel_execution, &"d".repeat(64)));
    let mut cancel_proof = cancel_execution
        .prepare_proof(&bundle, TTL, &mut rng)
        .unwrap();
    assert!(matches!(
        block_on(cancel_proof.prove(
            &PendingProofService,
            &parameters,
            1_048_576,
            future::ready(proof::Abort::Cancelled),
        )),
        Err(Error::Proof(proof::Error::Cancelled))
    ));
    assert!(matches!(
        block_on(cancel_proof.prove(&service, &parameters, 1_048_576, future::pending(),)),
        Err(Error::State)
    ));

    let drop_target =
        WitnessTarget::from_state_config(&bundle, state, &parameters, TTL, &mut rng).unwrap();
    let (drop_inputs, drop_context) =
        source_inputs_and_context(&control_plan, "14", &"e".repeat(64));
    let mut drop_execution = WitnessExecution::from_target(
        &bundle,
        drop_target,
        drop_inputs,
        drop_context,
        &parameters,
        TTL,
    )
    .unwrap();
    assert!(complete_source(&mut drop_execution, &"e".repeat(64)));
    let mut dropped_proof = drop_execution
        .prepare_proof(&bundle, TTL, &mut rng)
        .unwrap();
    block_on(async {
        let mut attempt = Box::pin(dropped_proof.prove(
            &PendingProofService,
            &parameters,
            1_048_576,
            future::pending(),
        ));
        assert!(futures::poll!(attempt.as_mut()).is_pending());
        drop(attempt);
    });
    assert!(matches!(
        block_on(dropped_proof.prove(&service, &parameters, 1_048_576, future::pending(),)),
        Err(Error::State)
    ));
}
