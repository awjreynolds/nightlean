#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Plan, check,
    control::{InvocationTarget, Session, TypedResponse},
    create_state, field_decimal, field_value,
    host::{self, Capability, Context, Limits, Operation, Provider},
    prepare,
    witness::{Parameter, WitnessSignature},
    zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use transient_crypto::{
    curve::{EmbeddedFr, EmbeddedGroupAffine, Fr},
    fab::AlignedValueExt,
};

fn artifacts(entry: &str) -> (&'static str, &'static str, &'static [u8]) {
    match entry {
        "registerWithKey" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.registerWithKey.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.registerWithKey.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.registerWithKey.zkir"
            ),
        ),
        "mint" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.mint.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.mint.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.mint.zkir"
            ),
        ),
        "sweep" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.sweep.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.sweep.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.sweep.zkir"
            ),
        ),
        "transfer" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.transfer.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.transfer.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.transfer.zkir"
            ),
        ),
        "burn" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.burn.witness.control.json"
            ),
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.burn.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.burn.zkir"
            ),
        ),
        _ => panic!("unknown confidential-token entrypoint {entry}"),
    }
}

fn view_artifacts(entry: &str) -> (&'static str, &'static [u8]) {
    match entry {
        "totalSupply" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.totalSupply.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.totalSupply.zkir"
            ),
        ),
        "isRegistered" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.isRegistered.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.isRegistered.zkir"
            ),
        ),
        "balanceOf" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.balanceOf.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.balanceOf.zkir"
            ),
        ),
        "pendingOf" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.pendingOf.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.pendingOf.zkir"
            ),
        ),
        "computeAccountId" => (
            include_str!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.computeAccountId.impact.json"
            ),
            include_bytes!(
                "fixtures/confidential-token/321/OpenZeppelinPort.ConfidentialToken.computeAccountId.zkir"
            ),
        ),
        _ => panic!("unknown confidential-token view {entry}"),
    }
}

fn signatures(plan: &Json) -> Vec<WitnessSignature> {
    plan["witnesses"]
        .as_array()
        .unwrap()
        .iter()
        .map(|value| WitnessSignature {
            name: value["name"].as_str().unwrap().to_owned(),
            operation: value["operation"].as_str().unwrap().to_owned(),
            capability: value["capability"].as_str().unwrap().to_owned(),
            parameters: value["parameters"]
                .as_array()
                .unwrap()
                .iter()
                .map(|parameter| Parameter {
                    name: parameter["name"].as_str().unwrap().to_owned(),
                    type_token: parameter["type"].as_str().unwrap().to_owned(),
                })
                .collect(),
            result_type: value["resultType"].as_str().unwrap().to_owned(),
            private_key: value["privateKey"].as_str().map(str::to_owned),
        })
        .collect()
}

fn context(plan: &Json, attempt_id: &str) -> Context {
    let mut operations = BTreeMap::<String, Operation>::new();
    let mut providers = Vec::new();
    let mut capabilities = BTreeMap::<String, (String, BTreeSet<String>)>::new();
    for signature in signatures(plan) {
        let mut argument_schema: BTreeMap<_, _> = signature
            .parameters
            .iter()
            .map(|parameter| (parameter.name.clone(), parameter.type_token.clone()))
            .collect();
        if signature.operation == host::READ {
            argument_schema.insert("key".into(), "Key".into());
        }
        let operation = Operation {
            operation: signature.operation.clone(),
            argument_schema,
            result_schema: signature.result_type.clone(),
        };
        if let Some(previous) = operations.insert(signature.operation.clone(), operation) {
            assert_eq!(
                previous.argument_schema,
                operations[&signature.operation].argument_schema
            );
            assert_eq!(previous.result_schema, signature.result_type);
        }
        let prefix = signature
            .private_key
            .as_deref()
            .and_then(|key| key.rsplit_once('/').map(|(root, _)| format!("{root}/")))
            .unwrap_or_else(|| "lookup/".into());
        let entry = capabilities
            .entry(signature.capability.clone())
            .or_insert_with(|| (prefix.clone(), BTreeSet::new()));
        assert_eq!(entry.0, prefix);
        entry.1.insert(signature.operation.clone());
        providers.push(Provider {
            input: signature.name,
            operation: signature.operation,
            capability: signature.capability,
            arguments: signature
                .private_key
                .map(|key| BTreeMap::from([("key".into(), json!(key))]))
                .unwrap_or_default(),
        });
    }
    let commit_prefix = "noctium/OpenZeppelinPort.Wallet/";
    let mut capability_list = capabilities
        .into_iter()
        .map(|(id, (key_prefix, operations))| Capability {
            id,
            namespace: "noctium".into(),
            key_prefix,
            operations: operations.into_iter().collect(),
        })
        .collect::<Vec<_>>();
    capability_list.push(Capability {
        id: "commit".into(),
        namespace: "noctium".into(),
        key_prefix: commit_prefix.into(),
        operations: vec![host::CAS.into()],
    });
    Context {
        protocol_version: 1,
        namespace: "noctium".into(),
        base_revision: "genesis-r0".into(),
        attempt_id: attempt_id.into(),
        capabilities: capability_list,
        operations: operations.into_values().collect(),
        providers,
        commit_capability: "commit".into(),
        limits: Limits::default(),
    }
}

fn bytes(value: &[u8; 32]) -> Json {
    json!({"kind":"bytes", "values":value.as_slice()})
}

fn point_json(point: EmbeddedGroupAffine) -> Json {
    json!({
        "kind":"jubjubPoint",
        "x":field_decimal(point.x().unwrap()),
        "y":field_decimal(point.y().unwrap())
    })
}

fn reply(request: &Json, attempt_id: &str, value: Json) -> TypedResponse {
    serde_json::from_value(json!({
        "protocolVersion":2,
        "requestId":request["requestId"],
        "attemptId":attempt_id,
        "outcome":"value",
        "operation":request["operation"],
        "capability":request["capability"],
        "schema":request["schema"],
        "value":value
    }))
    .unwrap()
}

fn source_inputs(plan: &Json, values: BTreeMap<String, Json>) -> BTreeMap<String, Json> {
    let declared: BTreeSet<_> = plan["inputs"]
        .as_array()
        .unwrap()
        .iter()
        .map(|input| input["name"].as_str().unwrap().to_owned())
        .collect();
    assert_eq!(declared, values.keys().cloned().collect());
    values
}

fn wallet_values(
    plan: &Json,
    account_secret: &[u8; 32],
    encryption_secret: &[u8; 32],
) -> BTreeMap<String, Json> {
    signatures(plan)
        .into_iter()
        .filter_map(|signature| {
            let key = signature.private_key?;
            let value = if key.ends_with("/accountSecret") {
                bytes(account_secret)
            } else if key.ends_with("/encryptionSecret") {
                bytes(encryption_secret)
            } else {
                panic!("unexpected wallet key {key}")
            };
            Some((key, value))
        })
        .collect()
}

#[derive(Clone, Copy)]
struct Ciphertext {
    c1: EmbeddedGroupAffine,
    c2: EmbeddedGroupAffine,
}

#[derive(Clone, Copy)]
struct Memo {
    ephemeral: EmbeddedGroupAffine,
    amount: Fr,
}

fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update(part);
    }
    digest.finalize().into()
}

fn tag(text: &str) -> [u8; 32] {
    assert!(text.len() <= 32);
    let mut result = [0; 32];
    result[..text.len()].copy_from_slice(text.as_bytes());
    result
}

fn scalar(parts: &[&[u8]]) -> EmbeddedFr {
    EmbeddedFr::from_le_bytes(&hash(parts)[..31]).unwrap()
}

fn encryption_scalar(secret: &[u8; 32]) -> EmbeddedFr {
    scalar(&[&tag("ElGamal:secretToScalar"), secret])
}

fn account_id(secret: &[u8; 32]) -> [u8; 32] {
    hash(&[secret])
}

fn epoch_hash(epoch: u64) -> [u8; 32] {
    let encoded = Fr::from(epoch).as_le_bytes();
    hash(&[&encoded])
}

fn coordinates(point: EmbeddedGroupAffine) -> [Fr; 2] {
    [point.x().unwrap(), point.y().unwrap()]
}

fn expected_credit(
    seed: &[u8; 32],
    recipient: &[u8; 32],
    recipient_key: EmbeddedGroupAffine,
    epoch: u64,
    amount: u64,
) -> (Ciphertext, Memo) {
    let generator = EmbeddedGroupAffine::generator();
    let count_hash = epoch_hash(epoch);
    let balance_randomizer = scalar(&[seed, &tag("credit_balance"), recipient, &count_hash]);
    let memo_randomizer = scalar(&[seed, &tag("credit_memo"), recipient, &count_hash]);
    let ciphertext = Ciphertext {
        c1: generator * balance_randomizer,
        c2: generator * EmbeddedFr::from(amount) + recipient_key * balance_randomizer,
    };
    let ephemeral = generator * memo_randomizer;
    let shared = recipient_key * memo_randomizer;
    let shared_digest = hash(&[
        &shared.x().unwrap().as_le_bytes(),
        &shared.y().unwrap().as_le_bytes(),
    ]);
    let mask_digest = hash(&[&shared_digest, &tag("OZ_CFT_ecdh_memo_v1")]);
    let mask = Fr::from_le_bytes(&mask_digest[..31]).unwrap();
    (
        ciphertext,
        Memo {
            ephemeral,
            amount: Fr::from(amount) + mask,
        },
    )
}

fn expected_debit(
    seed: &[u8; 32],
    owner: Ciphertext,
    owner_key: EmbeddedGroupAffine,
    amount: u64,
) -> Ciphertext {
    let generator = EmbeddedGroupAffine::generator();
    let randomizer = scalar(&[seed, &tag("debit_balance")]);
    let negative_randomizer = EmbeddedFr::from(0u64) - randomizer;
    let negative_one = EmbeddedFr::from(0u64) - EmbeddedFr::from(1u64);
    let value_point = generator * EmbeddedFr::from(amount);
    Ciphertext {
        c1: owner.c1 + generator * negative_randomizer,
        c2: owner.c2 + (value_point + owner_key * randomizer) * negative_one,
    }
}

fn decrypt_small(ciphertext: Ciphertext, secret: EmbeddedFr, maximum: u64) -> u64 {
    let negative_secret = EmbeddedFr::from(0u64) - secret;
    let message = ciphertext.c2 + ciphertext.c1 * negative_secret;
    let generator = EmbeddedGroupAffine::generator();
    (0..=maximum)
        .find(|candidate| generator * EmbeddedFr::from(*candidate) == message)
        .expect("test balance stays in the bounded discrete-log search range")
}

fn state_slot<'a>(plan: &Plan, state: &'a ChargedState<Db>, name: &str) -> &'a StateValue<Db> {
    let index = plan
        .state
        .iter()
        .position(|field| field.name == name)
        .unwrap();
    let StateValue::Array(root) = state.get_ref() else {
        panic!("expected root state array")
    };
    root.get(index).unwrap()
}

fn map_record(plan: &Plan, state: &ChargedState<Db>, name: &str, key: &[u8; 32]) -> Vec<Fr> {
    let StateValue::Map(map) = state_slot(plan, state, name) else {
        panic!("expected {name} map")
    };
    let key: AlignedValue = (*key).into();
    let value = map.get(&key).expect("account map entry");
    let StateValue::Cell(cell) = &*value else {
        panic!("expected {name} record cell")
    };
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    fields
}

fn assert_ciphertext(
    plan: &Plan,
    state: &ChargedState<Db>,
    map: &str,
    key: &[u8; 32],
    expected: Ciphertext,
) {
    let mut fields = coordinates(expected.c1).to_vec();
    fields.extend(coordinates(expected.c2));
    assert_eq!(
        map_record(plan, state, map, key),
        fields,
        "{map} ciphertext"
    );
}

fn assert_record(
    plan: &Plan,
    state: &ChargedState<Db>,
    map: &str,
    key: &[u8; 32],
    expected: &[Fr],
) {
    assert_eq!(map_record(plan, state, map, key), expected, "{map} record");
}

fn memo_records(plan: &Plan, state: &ChargedState<Db>, key: &[u8; 32]) -> (usize, Vec<Vec<Fr>>) {
    fn walk(node: &StateValue<Db>, output: &mut Vec<Vec<Fr>>) -> usize {
        let StateValue::Array(parts) = node else {
            panic!("expected native List array")
        };
        let StateValue::Cell(length) = parts.get(2).unwrap() else {
            panic!("expected List length cell")
        };
        let mut length_fields = Vec::new();
        length.value_only_field_repr(&mut length_fields);
        let declared: usize = field_decimal(length_fields[0]).parse().unwrap();
        if matches!(parts.get(0), Some(StateValue::Null)) {
            assert!(matches!(parts.get(1), Some(StateValue::Null)));
            assert_eq!(declared, 0);
            return 0;
        }
        let StateValue::Cell(record) = parts.get(0).unwrap() else {
            panic!("expected memo record cell")
        };
        let mut fields = Vec::new();
        record.value_only_field_repr(&mut fields);
        output.push(fields);
        let tail = walk(parts.get(1).unwrap(), output);
        assert_eq!(declared, tail + 1);
        tail + 1
    }

    let StateValue::Map(map) = state_slot(plan, state, "memos") else {
        panic!("expected memos map")
    };
    let key: AlignedValue = (*key).into();
    let value = map.get(&key).expect("memo list map entry");
    let mut records = Vec::new();
    let length = walk(&value, &mut records);
    (length, records)
}

fn attempt(number: u64) -> String {
    format!("{number:064x}")
}

fn run_entry(
    entry: &str,
    values: BTreeMap<String, Json>,
    account_secret: &[u8; 32],
    encryption_secret: &[u8; 32],
    seed: Option<[u8; 32]>,
    decrypt_balance: Option<Ciphertext>,
    attempt_number: u64,
    prior_state: &ChargedState<Db>,
) -> (ChargedState<Db>, BTreeMap<String, Json>) {
    let (control_text, native_text, circuit_bytes) = artifacts(entry);
    let control_plan: Json = serde_json::from_str(control_text).unwrap();
    let native_plan: Plan = serde_json::from_str(native_text).unwrap();
    let circuit = IrSource::load(circuit_bytes).unwrap();
    let source_inputs = source_inputs(&control_plan, values);
    let attempt_id = attempt(attempt_number);
    let binding: Json = serde_json::from_str(control_plan["binding"].as_str().unwrap()).unwrap();
    let digest = hex::encode(Sha256::digest(
        control_plan["binding"].as_str().unwrap().as_bytes(),
    ));
    let wallet = wallet_values(&control_plan, account_secret, encryption_secret);
    let mut session = Session::from_json_with_invocation_target(
        control_plan.clone(),
        source_inputs,
        context(&control_plan, &attempt_id),
        Some(&digest),
        Some(InvocationTarget {
            contract_address: "a".repeat(64),
            entrypoint: entry.into(),
        }),
    )
    .unwrap_or_else(|error| panic!("{entry}: {error:#}"));
    let mut callbacks = BTreeSet::new();
    let mut reads = BTreeSet::new();
    loop {
        let status = session.advance().unwrap();
        if status["status"] != "need_host" {
            assert_eq!(status["status"], "completed", "{entry}: {status}");
            break;
        }
        let request = &status["request"];
        let private = session.private_request().unwrap();
        let value = if request["operation"] == host::READ {
            let key = private["arguments"]["key"].as_str().unwrap();
            reads.insert(key.to_owned());
            wallet
                .get(key)
                .unwrap_or_else(|| panic!("missing wallet value for {key}"))
                .clone()
        } else {
            let name = request["name"].as_str().unwrap();
            callbacks.insert(name.to_owned());
            match name {
                "OpenZeppelinPort.freshSeed" => {
                    bytes(&seed.expect("seed callback needs deterministic test seed"))
                }
                "OpenZeppelinPort.plaintextBalance" => {
                    let expected =
                        decrypt_balance.expect("plaintext callback needs expected state balance");
                    assert_eq!(private["arguments"]["c1"], point_json(expected.c1));
                    assert_eq!(private["arguments"]["c2"], point_json(expected.c2));
                    let secret = encryption_scalar(encryption_secret);
                    json!(decrypt_small(expected, secret, 64).to_string())
                }
                other => panic!("unexpected witness callback {other}"),
            }
        };
        session
            .resume_typed(reply(request, &attempt_id, value))
            .unwrap();
    }
    let expected_reads = if wallet.is_empty() {
        BTreeSet::new()
    } else {
        wallet.keys().cloned().collect()
    };
    assert_eq!(reads, expected_reads, "{entry} wallet reads");
    let expected_callbacks: BTreeSet<String> = match entry {
        "mint" => ["OpenZeppelinPort.freshSeed".into()].into(),
        "transfer" | "burn" => [
            "OpenZeppelinPort.freshSeed".into(),
            "OpenZeppelinPort.plaintextBalance".into(),
        ]
        .into(),
        _ => BTreeSet::new(),
    };
    assert_eq!(callbacks, expected_callbacks, "{entry} callbacks");
    let relation = binding["nativeRelation"].clone();
    let completion = session.private_completion(&relation).unwrap();
    let native_inputs: BTreeMap<String, Json> =
        serde_json::from_value(completion["inputs"].clone()).unwrap();
    let execution = prepare(
        &native_plan,
        &native_inputs,
        prior_state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).unwrap();
    (execution.after.state.clone(), native_inputs)
}

fn initial_state(plan: &Plan) -> ChargedState<Db> {
    create_state(
        plan,
        &BTreeMap::from([
            ("encryptionKeys".into(), json!([])),
            ("balances".into(), json!([])),
            ("pending".into(), json!([])),
            ("memos".into(), json!([])),
            ("creditEpochs".into(), json!([])),
            ("initialized".into(), json!(true)),
            ("totalSupply".into(), json!("0")),
        ]),
    )
    .unwrap()
}

fn view(
    entry: &str,
    account: Option<&[u8; 32]>,
    state: &ChargedState<Db>,
) -> BTreeMap<String, Json> {
    let (plan_text, circuit_bytes) = view_artifacts(entry);
    let plan: Plan = serde_json::from_str(plan_text).unwrap();
    let circuit = IrSource::load(circuit_bytes).unwrap();
    let inputs = match entry {
        "totalSupply" => BTreeMap::new(),
        "computeAccountId" => BTreeMap::from([(
            "secret".into(),
            bytes(account.expect("computeAccountId needs a secret")),
        )]),
        _ => BTreeMap::from([(
            "account".into(),
            bytes(account.expect("account view needs an account")),
        )]),
    };
    let execution = prepare(
        &plan,
        &inputs,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).unwrap();
    execution.returns_json()
}

fn assert_rejects_candidate_mismatch(
    plan: &Plan,
    circuit: &IrSource,
    inputs: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
    actual: Ciphertext,
    owner_key: EmbeddedGroupAffine,
) {
    let mut changed = inputs.clone();
    // Rerandomize to valid subgroup points with the same plaintext, but a different ledger record.
    let alternate = Ciphertext {
        c1: actual.c1 + EmbeddedGroupAffine::generator(),
        c2: actual.c2 + owner_key,
    };
    for (name, value) in ["balanceC1X", "balanceC1Y", "balanceC2X", "balanceC2Y"]
        .into_iter()
        .zip([
            alternate.c1.x().unwrap(),
            alternate.c1.y().unwrap(),
            alternate.c2.x().unwrap(),
            alternate.c2.y().unwrap(),
        ])
    {
        changed.insert(name.into(), json!(field_decimal(value)));
    }
    let execution = prepare(
        plan,
        &changed,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .expect("valid alternate ciphertext should prepare before ledger binding is checked");
    assert!(
        check(&execution, circuit).is_err(),
        "candidate ciphertext mismatch passed native relation"
    );
}

#[test]
fn confidential_token_registration_pending_sweep_and_transfer_use_native_relations() {
    // These deterministic seeds and keys exercise test plumbing only. They do not establish
    // production seed freshness or production confidentiality.
    let alice_account_secret = [17u8; 32];
    let alice_encryption_secret = [7u8; 32];
    let bob_account_secret = [18u8; 32];
    let bob_encryption_secret = [8u8; 32];
    let alice = account_id(&alice_account_secret);
    let bob = account_id(&bob_account_secret);
    let missing_account_secret = [19u8; 32];
    let missing = account_id(&missing_account_secret);
    let alice_key_scalar = encryption_scalar(&alice_encryption_secret);
    let bob_key_scalar = encryption_scalar(&bob_encryption_secret);
    let generator = EmbeddedGroupAffine::generator();
    let alice_key = generator * alice_key_scalar;
    let bob_key = generator * bob_key_scalar;
    let identity = generator * EmbeddedFr::from(0u64);

    let (_, register_text, _) = artifacts("registerWithKey");
    let register_plan: Plan = serde_json::from_str(register_text).unwrap();
    let mut state = initial_state(&register_plan);
    assert_eq!(
        state_slot(&register_plan, &state, "initialized"),
        &StateValue::Cell(storage::arena::Sp::new(field_value(Fr::from(1u64))))
    );

    for (sequence, account, account_secret, encryption_secret, public_key) in [
        (
            1,
            alice,
            &alice_account_secret,
            &alice_encryption_secret,
            alice_key,
        ),
        (2, bob, &bob_account_secret, &bob_encryption_secret, bob_key),
    ] {
        let values = BTreeMap::from([
            ("accountId".into(), bytes(&account)),
            ("pk".into(), point_json(public_key)),
        ]);
        state = run_entry(
            "registerWithKey",
            values,
            account_secret,
            encryption_secret,
            None,
            None,
            sequence,
            &state,
        )
        .0;
        assert_record(
            &register_plan,
            &state,
            "encryptionKeys",
            &account,
            &coordinates(public_key),
        );
        assert_ciphertext(
            &register_plan,
            &state,
            "balances",
            &account,
            Ciphertext {
                c1: identity,
                c2: identity,
            },
        );
        assert_ciphertext(
            &register_plan,
            &state,
            "pending",
            &account,
            Ciphertext {
                c1: identity,
                c2: identity,
            },
        );
    }

    let (_, mint_text, _) = artifacts("mint");
    let mint_plan: Plan = serde_json::from_str(mint_text).unwrap();
    let pending_before = map_record(&mint_plan, &state, "pending", &alice);
    assert_eq!(pending_before.len(), 4);
    let mint_seed = [0x31u8; 32];
    let (pending_after_mint, mint_memo) = expected_credit(&mint_seed, &alice, alice_key, 1, 12);
    let mut mint_values = BTreeMap::from([
        ("recipient".into(), bytes(&alice)),
        ("value".into(), json!("12")),
        ("recipientPk".into(), point_json(alice_key)),
        ("epoch".into(), json!("1")),
    ]);
    for (name, value) in ["previousC1X", "previousC1Y", "previousC2X", "previousC2Y"]
        .into_iter()
        .zip(pending_before)
    {
        mint_values.insert(name.into(), json!(field_decimal(value)));
    }
    state = run_entry(
        "mint",
        mint_values,
        &alice_account_secret,
        &alice_encryption_secret,
        Some(mint_seed),
        None,
        3,
        &state,
    )
    .0;
    assert_ciphertext(
        &mint_plan,
        &state,
        "balances",
        &alice,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_ciphertext(&mint_plan, &state, "pending", &alice, pending_after_mint);
    assert_eq!(memo_records(&mint_plan, &state, &alice).0, 1);
    assert_eq!(
        memo_records(&mint_plan, &state, &alice).1[0],
        [
            mint_memo.ephemeral.x().unwrap(),
            mint_memo.ephemeral.y().unwrap(),
            mint_memo.amount,
        ]
    );
    assert_eq!(
        map_record(&mint_plan, &state, "creditEpochs", &alice),
        vec![Fr::from(1u64)]
    );
    assert_eq!(
        field_decimal({
            let StateValue::Cell(cell) = state_slot(&mint_plan, &state, "totalSupply") else {
                panic!("expected totalSupply cell")
            };
            let mut fields = Vec::new();
            cell.value_only_field_repr(&mut fields);
            fields[0]
        }),
        "12"
    );

    let (_, sweep_text, _) = artifacts("sweep");
    let sweep_plan: Plan = serde_json::from_str(sweep_text).unwrap();
    let balance_before = map_record(&sweep_plan, &state, "balances", &alice);
    let pending_before_sweep = map_record(&sweep_plan, &state, "pending", &alice);
    let mut sweep_values = BTreeMap::from([("accountId".into(), bytes(&alice))]);
    for (name, value) in ["balanceC1X", "balanceC1Y", "balanceC2X", "balanceC2Y"]
        .into_iter()
        .zip(balance_before)
        .chain(
            ["pendingC1X", "pendingC1Y", "pendingC2X", "pendingC2Y"]
                .into_iter()
                .zip(pending_before_sweep),
        )
    {
        sweep_values.insert(name.into(), json!(field_decimal(value)));
    }
    state = run_entry(
        "sweep",
        sweep_values,
        &alice_account_secret,
        &alice_encryption_secret,
        None,
        None,
        4,
        &state,
    )
    .0;
    let spendable = pending_after_mint;
    assert_ciphertext(&sweep_plan, &state, "balances", &alice, spendable);
    assert_ciphertext(
        &sweep_plan,
        &state,
        "pending",
        &alice,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_eq!(memo_records(&sweep_plan, &state, &alice).0, 1);

    let (_, transfer_text, transfer_bytes) = artifacts("transfer");
    let transfer_plan: Plan = serde_json::from_str(transfer_text).unwrap();
    let transfer_circuit = IrSource::load(transfer_bytes).unwrap();
    let state_before_transfer = state.clone();
    let balance_before_transfer = map_record(&transfer_plan, &state, "balances", &alice);
    let recipient_pending_before = map_record(&transfer_plan, &state, "pending", &bob);
    let transfer_seed = [0x32u8; 32];
    let owner_after = expected_debit(&transfer_seed, spendable, alice_key, 5);
    let (recipient_after, transfer_memo) = expected_credit(&transfer_seed, &bob, bob_key, 1, 5);
    let mut transfer_values = BTreeMap::from([
        ("accountId".into(), bytes(&alice)),
        ("recipient".into(), bytes(&bob)),
        ("value".into(), json!("5")),
        ("recipientPk".into(), point_json(bob_key)),
        ("epoch".into(), json!("1")),
    ]);
    for (name, value) in ["balanceC1X", "balanceC1Y", "balanceC2X", "balanceC2Y"]
        .into_iter()
        .zip(balance_before_transfer)
        .chain(
            ["pendingC1X", "pendingC1Y", "pendingC2X", "pendingC2Y"]
                .into_iter()
                .zip(recipient_pending_before),
        )
    {
        transfer_values.insert(name.into(), json!(field_decimal(value)));
    }
    let (after_transfer, transfer_inputs) = run_entry(
        "transfer",
        transfer_values,
        &alice_account_secret,
        &alice_encryption_secret,
        Some(transfer_seed),
        Some(spendable),
        5,
        &state,
    );
    assert_ciphertext(
        &transfer_plan,
        &after_transfer,
        "balances",
        &alice,
        owner_after,
    );
    assert_ciphertext(
        &transfer_plan,
        &after_transfer,
        "pending",
        &bob,
        recipient_after,
    );
    assert_ciphertext(
        &transfer_plan,
        &after_transfer,
        "balances",
        &bob,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_eq!(decrypt_small(owner_after, alice_key_scalar, 64), 7);
    assert_eq!(decrypt_small(recipient_after, bob_key_scalar, 64), 5);
    assert_eq!(
        decrypt_small(
            Ciphertext {
                c1: identity,
                c2: identity
            },
            bob_key_scalar,
            64
        ),
        0
    );
    assert_eq!(memo_records(&transfer_plan, &after_transfer, &alice).0, 1);
    assert_eq!(memo_records(&transfer_plan, &after_transfer, &bob).0, 1);
    assert_eq!(
        memo_records(&transfer_plan, &after_transfer, &bob).1[0],
        [
            transfer_memo.ephemeral.x().unwrap(),
            transfer_memo.ephemeral.y().unwrap(),
            transfer_memo.amount,
        ]
    );
    assert_eq!(
        map_record(&transfer_plan, &after_transfer, "creditEpochs", &bob),
        vec![Fr::from(1u64)]
    );
    assert_rejects_candidate_mismatch(
        &transfer_plan,
        &transfer_circuit,
        &transfer_inputs,
        &state_before_transfer,
        spendable,
        alice_key,
    );

    state = after_transfer.clone();
    let (_, burn_text, _) = artifacts("burn");
    let burn_plan: Plan = serde_json::from_str(burn_text).unwrap();
    let burn_seed = [0x33u8; 32];
    let balance_before_burn = map_record(&burn_plan, &state, "balances", &alice);
    let balance_after_burn = expected_debit(&burn_seed, owner_after, alice_key, 2);
    let mut burn_values = BTreeMap::from([
        ("accountId".into(), bytes(&alice)),
        ("value".into(), json!("2")),
    ]);
    for (name, value) in ["balanceC1X", "balanceC1Y", "balanceC2X", "balanceC2Y"]
        .into_iter()
        .zip(balance_before_burn)
    {
        burn_values.insert(name.into(), json!(field_decimal(value)));
    }
    state = run_entry(
        "burn",
        burn_values,
        &alice_account_secret,
        &alice_encryption_secret,
        Some(burn_seed),
        Some(owner_after),
        6,
        &state,
    )
    .0;
    assert_ciphertext(&burn_plan, &state, "balances", &alice, balance_after_burn);
    assert_eq!(decrypt_small(balance_after_burn, alice_key_scalar, 64), 5);
    assert_ciphertext(
        &burn_plan,
        &state,
        "pending",
        &alice,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_ciphertext(&burn_plan, &state, "pending", &bob, recipient_after);
    assert_ciphertext(
        &burn_plan,
        &state,
        "balances",
        &bob,
        Ciphertext {
            c1: identity,
            c2: identity,
        },
    );
    assert_eq!(
        memo_records(&burn_plan, &state, &alice),
        memo_records(&burn_plan, &after_transfer, &alice)
    );
    assert_eq!(
        memo_records(&burn_plan, &state, &bob),
        memo_records(&burn_plan, &after_transfer, &bob)
    );
    assert_eq!(
        map_record(&burn_plan, &state, "creditEpochs", &alice),
        vec![Fr::from(1u64)]
    );
    assert_eq!(
        map_record(&burn_plan, &state, "creditEpochs", &bob),
        vec![Fr::from(1u64)]
    );

    assert_eq!(view("totalSupply", None, &state)["supply"], "10");
    assert_eq!(view("isRegistered", Some(&alice), &state)["value"], true);
    assert_eq!(view("isRegistered", Some(&missing), &state)["value"], false);
    let alice_balance = view("balanceOf", Some(&alice), &state);
    assert_eq!(alice_balance["c1"], point_json(balance_after_burn.c1));
    assert_eq!(alice_balance["c2"], point_json(balance_after_burn.c2));
    assert_eq!(decrypt_small(balance_after_burn, alice_key_scalar, 64), 5);
    let bob_pending = view("pendingOf", Some(&bob), &state);
    assert_eq!(bob_pending["c1"], point_json(recipient_after.c1));
    assert_eq!(bob_pending["c2"], point_json(recipient_after.c2));
    assert_eq!(decrypt_small(recipient_after, bob_key_scalar, 64), 5);
    assert_eq!(
        view("balanceOf", Some(&missing), &state),
        BTreeMap::from([
            ("c1".into(), point_json(identity)),
            ("c2".into(), point_json(identity)),
        ])
    );
    assert_eq!(
        view("pendingOf", Some(&missing), &state),
        BTreeMap::from([
            ("c1".into(), point_json(identity)),
            ("c2".into(), point_json(identity)),
        ])
    );
    assert_eq!(
        view("computeAccountId", Some(&alice_account_secret), &state)["accountId"],
        bytes(&alice)
    );
}
