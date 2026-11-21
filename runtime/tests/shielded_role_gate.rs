#![cfg(feature = "zkir-321")]

use base_crypto::{fab::AlignedValue, hash::HashOutput};
use noctium_runtime::{
    Db, Expr, Plan, Value as RuntimeValue, check,
    control::{InvocationTarget, Session, TypedResponse},
    create_state, evaluate, field_decimal,
    host::{self, Capability, Context, Limits, Operation, Provider},
    merkle::merkle_tree_at,
    prepare,
    witness::{Parameter, WitnessSignature},
    zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{
    collections::{BTreeMap, BTreeSet},
    env, fs,
    path::PathBuf,
};
use storage::{arena::Sp, storage::HashMap};
use transient_crypto::{
    curve::Fr,
    fab::AlignedValueExt,
    hash::{degrade_to_transient, transient_hash},
    merkle_tree::MerkleTree,
};

#[derive(Clone, Copy, Debug)]
enum Case {
    Accepted,
    WrongLeaf,
    WrongRoot,
    Revoked,
}

#[derive(Debug)]
struct Failure {
    stage: &'static str,
    message: String,
}

impl Failure {
    fn new(stage: &'static str, error: impl std::fmt::Display) -> Self {
        Self {
            stage,
            message: error.to_string(),
        }
    }
}

struct Fixture {
    control: Json,
    plan: Plan,
    relation: IrSource,
}

fn fixture() -> Fixture {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_SHIELDED_ROLE_GATE_DIR")
            .expect("set fresh artifacts in NOCTIUM_SHIELDED_ROLE_GATE_DIR"),
    );
    let stem = "OpenZeppelinPort.ShieldedRoleGate.ShieldedRoleGate.protectedAction";
    let control: Json = serde_json::from_slice(
        &fs::read(directory.join(format!("{stem}.witness.control.json"))).unwrap(),
    )
    .unwrap();
    let plan =
        serde_json::from_slice(&fs::read(directory.join(format!("{stem}.impact.json"))).unwrap())
            .unwrap();
    let relation = IrSource::load(
        fs::read(directory.join(format!("{stem}.zkir")))
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    Fixture {
        control,
        plan,
        relation,
    }
}

fn bytes32(start: u8) -> [u8; 32] {
    std::array::from_fn(|index| start + index as u8)
}

fn bytes_json(value: &[u8; 32]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn persistent_hash_vector32(values: &[[u8; 32]]) -> [u8; 32] {
    let values = values
        .iter()
        .map(|value| Expr::Bytes32Literal {
            values: value.to_vec(),
        })
        .collect();
    let RuntimeValue::Bytes(hash) =
        evaluate(&Expr::PersistentHashVector32 { values }, &BTreeMap::new()).unwrap()
    else {
        panic!("persistent hash vector returns Bytes32")
    };
    hash.try_into().expect("persistent hash is Bytes32")
}

fn role_values() -> ([u8; 32], [u8; 32], [u8; 32], [u8; 32], [u8; 32]) {
    let (salt, secret, role) = (bytes32(0xa0), bytes32(0x20), bytes32(0x60));
    let domain = |value: &str| {
        assert!(value.len() <= 32);
        let mut bytes = [0; 32];
        bytes[..value.len()].copy_from_slice(value.as_bytes());
        bytes
    };
    let account =
        persistent_hash_vector32(&[secret, salt, domain("ShieldedAccessControl:accountId")]);
    let commitment = persistent_hash_vector32(&[
        role,
        account,
        salt,
        domain("ShieldedAccessControl:commitment"),
    ]);
    let nullifier =
        persistent_hash_vector32(&[commitment, domain("ShieldedAccessControl:nullifier")]);
    assert_eq!(
        hex::encode(account),
        "2a48525bf785635d19fd2c665f3d36311d18f276b6fe33212062a99420a0f912"
    );
    assert_eq!(
        hex::encode(commitment),
        "58d08cab6386bc8fa916e81b88c07e6e74d5df4e777f5de0c145372a3e7f0e59"
    );
    assert_eq!(
        hex::encode(nullifier),
        "9bcb8b214284661706ff8df432f7a3c121954456849992efbdc35875128f2083"
    );
    (salt, secret, role, commitment, nullifier)
}

fn leaf_digest(leaf: &[u8; 32]) -> [u8; 32] {
    let mut digest = Sha256::new();
    digest.update(b"mdn:lh");
    digest.update(leaf);
    digest.finalize().into()
}

fn tree_state(leaves: &[[u8; 32]]) -> StateValue<Db> {
    let mut tree = MerkleTree::<(), Db>::blank(20);
    for (index, leaf) in leaves.iter().enumerate() {
        tree = tree
            .try_update_hash(index as u64, HashOutput(leaf_digest(leaf)), ())
            .unwrap();
    }
    StateValue::Array(
        vec![
            StateValue::BoundedMerkleTree(tree.rehash()),
            StateValue::Cell(Sp::new(AlignedValue::from(leaves.len() as u64))),
        ]
        .into(),
    )
}

fn state_slot(plan: &Plan, name: &str) -> usize {
    plan.state
        .iter()
        .position(|declaration| declaration.name == name)
        .unwrap_or_else(|| panic!("missing {name} state declaration"))
}

fn plan_state(
    plan: &Plan,
    salt: [u8; 32],
    leaf: [u8; 32],
    nullifier: [u8; 32],
    revoked: bool,
) -> ChargedState<Db> {
    let initial = create_state(
        plan,
        &BTreeMap::from([
            ("instanceSalt".into(), bytes_json(&salt)),
            ("operatorRoles".into(), json!([])),
            ("revokedRoleNullifiers".into(), json!([])),
            ("protectedActions".into(), json!("0")),
        ]),
    )
    .unwrap();
    let StateValue::Array(slots) = initial.get_ref() else {
        panic!("expected contract state array")
    };
    let slots = slots
        .clone()
        .insert(
            state_slot(plan, "operatorRoles"),
            tree_state(&[bytes32(0x40), leaf]),
        )
        .unwrap();
    let revoked_values = if revoked {
        HashMap::new().insert(AlignedValue::from(nullifier), StateValue::Null)
    } else {
        HashMap::new()
    };
    let slots = slots
        .insert(
            state_slot(plan, "revokedRoleNullifiers"),
            StateValue::Map(revoked_values),
        )
        .unwrap();
    ChargedState::new(StateValue::Array(slots))
}

fn counter_value(state: &ChargedState<Db>, plan: &Plan) -> String {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected contract state array")
    };
    let StateValue::Cell(value) = slots.get(state_slot(plan, "protectedActions")).unwrap() else {
        panic!("expected protectedActions counter cell")
    };
    let mut fields = Vec::new();
    value.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

fn signatures(control: &Json) -> Vec<WitnessSignature> {
    control["witnesses"]
        .as_array()
        .expect("typed witness list")
        .iter()
        .map(|value| WitnessSignature {
            name: value["name"].as_str().unwrap().into(),
            operation: value["operation"].as_str().unwrap().into(),
            capability: value["capability"].as_str().unwrap().into(),
            parameters: value["parameters"]
                .as_array()
                .unwrap()
                .iter()
                .map(|parameter| Parameter {
                    name: parameter["name"].as_str().unwrap().into(),
                    type_token: parameter["type"].as_str().unwrap().into(),
                })
                .collect(),
            result_type: value["resultType"].as_str().unwrap().into(),
            private_key: value["privateKey"].as_str().map(str::to_owned),
        })
        .collect()
}

fn source_context(signatures: &[WitnessSignature], attempt_id: &str) -> Context {
    assert_eq!(signatures.len(), 2, "fixture has two typed callbacks");
    assert!(signatures.iter().all(|s| s.private_key.is_none()));
    assert_eq!(
        signatures
            .iter()
            .map(|s| &s.capability)
            .collect::<BTreeSet<_>>()
            .len(),
        signatures.len(),
        "each callback has its own capability"
    );
    let operations = signatures
        .iter()
        .map(|signature| Operation {
            operation: signature.operation.clone(),
            argument_schema: signature
                .parameters
                .iter()
                .map(|p| (p.name.clone(), p.type_token.clone()))
                .collect(),
            result_schema: signature.result_type.clone(),
        })
        .collect();
    let providers = signatures
        .iter()
        .map(|signature| Provider {
            input: signature.name.clone(),
            operation: signature.operation.clone(),
            capability: signature.capability.clone(),
            arguments: BTreeMap::new(),
        })
        .collect();
    let mut capabilities: Vec<_> = signatures
        .iter()
        .map(|signature| Capability {
            id: signature.capability.clone(),
            namespace: "noctium".into(),
            key_prefix: "lookup/".into(),
            operations: vec![signature.operation.clone()],
        })
        .collect();
    capabilities.extend([
        Capability {
            id: "private".into(),
            namespace: "noctium".into(),
            key_prefix: "cache/".into(),
            operations: vec![host::STAGE.into()],
        },
        Capability {
            id: "commit".into(),
            namespace: "noctium".into(),
            key_prefix: "cache/".into(),
            operations: vec![host::CAS.into()],
        },
    ]);
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "shielded-role-gate-test".into(),
        attempt_id: attempt_id.into(),
        capabilities,
        operations,
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn binding(control: &Json) -> Json {
    serde_json::from_str(control["binding"].as_str().unwrap()).unwrap()
}

fn assert_disclosure(control: &Json) {
    let binding = binding(control);
    assert_eq!(
        binding["inputBindings"],
        json!([
            {"inputs":["role"],"name":"role","type":"Bytes<32>"},
            {"inputs":["instanceSalt"],"name":"instanceSalt","type":"Bytes<32>"}
        ])
    );
    assert_eq!(
        binding["ledgerInputs"],
        json!([
            {"name":"_noctium_bytes_configuredSalt_0","type":"UIntRange<256>","visibility":"public"},
            {"name":"_noctium_bytes_configuredSalt_1","type":"UIntRange<452312848583266388373324160190187140051835877600158453279131187530910662656>","visibility":"public"},
            {"name":"rootMatches","type":"Bool","visibility":"public"},
            {"name":"isRevoked","type":"Bool","visibility":"public"}
        ])
    );
    let inputs = binding["circuitInputs"].as_array().unwrap();
    assert_eq!(inputs.len(), 75);
    assert_eq!(
        inputs[0],
        json!({"name":"role","type":"Bytes<32>","visibility":"public"})
    );
    assert_eq!(
        inputs[1],
        json!({"name":"instanceSalt","type":"Bytes<32>","visibility":"public"})
    );
    assert!(
        inputs[2..]
            .iter()
            .all(|input| input["visibility"] == "private")
    );
    let outputs: Vec<String> = binding["circuitOutputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|output| output["name"].as_str().unwrap().to_owned())
        .collect();
    let expected = std::iter::once("result.candidateRoot".to_owned())
        .chain((0..32).map(|index| format!("result.nullifier.{index}")))
        .collect::<Vec<_>>();
    assert_eq!(outputs, expected);
}

fn bound_session(control: &Json, salt: &[u8; 32], role: &[u8; 32], attempt_id: &str) -> Session {
    let digest = hex::encode(Sha256::digest(
        control["binding"].as_str().unwrap().as_bytes(),
    ));
    let entrypoint = binding(control)["target"]["entrypoint"]
        .as_str()
        .unwrap()
        .to_owned();
    Session::from_json_with_invocation_target(
        control.clone(),
        BTreeMap::from([
            ("instanceSalt".into(), bytes_json(salt)),
            ("role".into(), bytes_json(role)),
        ]),
        source_context(&signatures(control), attempt_id),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint,
        }),
    )
    .unwrap()
}

fn reply(request: &Json, attempt_id: &str, value: Json) -> TypedResponse {
    serde_json::from_value(json!({
        "protocolVersion":2, "requestId":request["requestId"], "attemptId":attempt_id,
        "outcome":"value", "operation":request["operation"],
        "capability":request["capability"], "schema":request["schema"], "value":value,
    }))
    .unwrap()
}

fn bytes_from_json(value: &Json) -> [u8; 32] {
    value["values"]
        .as_array()
        .expect("Bytes32 values")
        .iter()
        .map(|byte| byte.as_u64().unwrap() as u8)
        .collect::<Vec<_>>()
        .try_into()
        .expect("exact Bytes32 width")
}

fn path_payload(
    leaf: &[u8; 32],
    entries: &[transient_crypto::merkle_tree::MerklePathEntry],
) -> Json {
    json!({
        "kind":"struct", "id":"ShieldedRolePath", "fields":[
            {"name":"leaf","value":bytes_json(leaf)},
            {"name":"path","value":{"kind":"vector","items":entries.iter().map(|entry| json!({
                "kind":"struct","id":"MerkleTreePathEntry","fields":[
                    {"name":"sibling","value":{"kind":"struct","id":"MerkleTreeDigest","fields":[
                        {"name":"field","value":{"kind":"native","value":field_decimal(entry.sibling.0)}}
                    ]}},
                    {"name":"goes_left","value":{"kind":"bool","value":entry.goes_left}}
                ]
            })).collect::<Vec<_>>()}}
        ]
    })
}

fn execute(fixture: &Fixture, case: Case) -> Result<noctium_runtime::Execution, Failure> {
    let (salt, secret, role, commitment, nullifier) = role_values();
    let leaf = if matches!(case, Case::WrongLeaf) {
        bytes32(0xd0)
    } else {
        commitment
    };
    let state = plan_state(
        &fixture.plan,
        salt,
        leaf,
        nullifier,
        matches!(case, Case::Revoked),
    );
    assert_eq!(counter_value(&state, &fixture.plan), "0");
    let before = state.clone();
    let snapshot = merkle_tree_at(&fixture.plan.state, &state, "operatorRoles", &[])
        .map_err(|error| Failure::new("prepare", error))?;
    let path = snapshot
        .prehashed_path(1, leaf_digest(&leaf))
        .map_err(|error| Failure::new("prepare", error))?;
    assert_eq!(path.entries().len(), 20);
    assert!(
        !path.entries()[0].goes_left,
        "index 1 takes the right branch"
    );
    assert!(path.entries()[1..].iter().all(|entry| entry.goes_left));
    assert_eq!(
        field_decimal(path.entries()[0].sibling.0),
        "61795097227014194265404484167282283566548153069618789759326111531147211732"
    );
    assert!(
        path.entries()[1..]
            .iter()
            .all(|entry| entry.sibling.0 == Fr::from(0u64))
    );
    let expected_state_root = if matches!(case, Case::WrongLeaf) {
        "50512982715628251576640643497157979420700631529460322706458279278141824686830"
    } else {
        "52189801469605183362511379495446935355081063660435760300767912973492724363764"
    };
    let mut entries = path.entries().to_vec();
    if matches!(case, Case::WrongRoot) {
        entries[0].sibling.0 = entries[0].sibling.0 + Fr::from(1u64);
    }
    let witness_root = entries.iter().fold(
        degrade_to_transient(HashOutput(leaf_digest(&leaf))),
        |child, entry| {
            let sibling = entry.sibling.0;
            if entry.goes_left {
                transient_hash(&[child, sibling])
            } else {
                transient_hash(&[sibling, child])
            }
        },
    );
    assert_eq!(
        field_decimal(witness_root),
        if matches!(case, Case::WrongRoot) {
            "35768283892993510719832516690494894209335990020149980887956145720525902360836"
        } else {
            expected_state_root
        }
    );

    let attempt_id = format!("{:064x}", case as u8 + 1);
    let mut session = bound_session(&fixture.control, &salt, &role, &attempt_id);
    let mut callbacks = Vec::new();
    loop {
        let status = session
            .advance()
            .map_err(|error| Failure::new("witness", error))?;
        match status["status"].as_str() {
            Some("completed") => break,
            Some("failed") => {
                assert_eq!(
                    state, before,
                    "rejected witness leaves ledger state unchanged"
                );
                return Err(Failure::new("witness", status));
            }
            Some("need_host") => {
                let request = &status["request"];
                let private = session
                    .private_request()
                    .map_err(|error| Failure::new("witness", error))?;
                let name = request["name"].as_str().unwrap_or_default();
                let value = if name.ends_with("shieldedSecret") {
                    callbacks.push("shieldedSecret");
                    bytes_json(&secret)
                } else if name.ends_with("roleCommitmentPath") {
                    callbacks.push("roleCommitmentPath");
                    assert_eq!(
                        bytes_from_json(&private["arguments"]["commitment"]),
                        commitment
                    );
                    path_payload(&leaf, &entries)
                } else {
                    return Err(Failure::new(
                        "witness",
                        format!("unexpected callback {name}"),
                    ));
                };
                session
                    .resume_typed(reply(request, &attempt_id, value))
                    .map_err(|error| Failure::new("witness", error))?;
            }
            other => {
                return Err(Failure::new(
                    "witness",
                    format!("unexpected session status {other:?}: {status}"),
                ));
            }
        }
    }
    callbacks.sort_unstable();
    assert_eq!(callbacks, ["roleCommitmentPath", "shieldedSecret"]);
    let binding = binding(&fixture.control);
    let completion = session
        .private_completion(&binding["nativeRelation"])
        .map_err(|error| Failure::new("witness", error))?;
    let native_inputs: BTreeMap<String, Json> =
        serde_json::from_value(completion["inputs"].clone())
            .map_err(|error| Failure::new("witness", error))?;
    let execution = prepare(
        &fixture.plan,
        &native_inputs,
        &state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .map_err(|error| {
        assert_eq!(
            state, before,
            "rejected preparation leaves ledger state unchanged"
        );
        Failure::new("prepare", error)
    })?;
    check(&execution, &fixture.relation).map_err(|error| {
        assert_eq!(
            state, before,
            "rejected relation leaves ledger state unchanged"
        );
        Failure::new("relation", error)
    })?;
    Ok(execution)
}

fn assert_rejected(fixture: &Fixture, case: Case, stages: &[&str]) {
    match execute(fixture, case) {
        Ok(_) => panic!("{case:?} was accepted"),
        Err(failure) => {
            assert!(stages.contains(&failure.stage), "{failure:?}");
            assert!(!failure.message.is_empty(), "{failure:?}");
        }
    }
}

#[test]
#[ignore = "requires fresh ShieldedRoleGate outputs in NOCTIUM_SHIELDED_ROLE_GATE_DIR"]
fn shielded_role_gate_checks_a_private_depth_20_path_and_rejects_invalid_authorization() {
    let fixture = fixture();
    assert_disclosure(&fixture.control);

    let accepted = execute(&fixture, Case::Accepted).unwrap();
    assert_eq!(counter_value(&accepted.after.state, &fixture.plan), "1");
    assert_rejected(&fixture, Case::WrongLeaf, &["witness", "relation"]);
    assert_rejected(&fixture, Case::WrongRoot, &["prepare", "relation"]);
    assert_rejected(&fixture, Case::Revoked, &["prepare", "relation"]);
}
