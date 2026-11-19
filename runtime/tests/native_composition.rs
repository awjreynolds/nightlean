#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use ledger::structure::{ContractDeploy, INITIAL_PARAMETERS, LedgerState, ProofPreimageVersioned};
use noctium_runtime::{
    Db, Plan,
    artifacts::{Role, VerifiedBundle, verify},
    assembly::{CheckedNativeCall, assemble_checked_calls},
    check, create_state, prepare,
    proof::{CompositionMaterial, PreparedComposition, TrustedParameters},
    zkir::IrSource,
};
use onchain_runtime::{
    context::QueryContext,
    state::{ChargedState, ContractOperation, ContractState, EntryPointBuf},
};
use rand::rngs::OsRng;
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};
use transient_crypto::{
    curve::Fr,
    proofs::{VerifierKey, Zkir},
};

fn caller_fixture() -> (Plan, IrSource) {
    (
        serde_json::from_str(include_str!(
            "fixtures/native-call-claims/321/NativeCallClaims.claim.impact.json"
        ))
        .unwrap(),
        IrSource::load(
            include_bytes!("fixtures/native-call-claims/321/NativeCallClaims.claim.zkir")
                .as_slice(),
        )
        .unwrap(),
    )
}

fn callee_fixture() -> (Plan, IrSource) {
    (
        serde_json::from_str(include_str!(
            "fixtures/native-returns/321/NativeReturns.advance.impact.json"
        ))
        .unwrap(),
        IrSource::load(
            include_bytes!("fixtures/native-returns/321/NativeReturns.advance.zkir").as_slice(),
        )
        .unwrap(),
    )
}

fn bytes32(value: HashOutput) -> Json {
    json!({"kind":"bytes", "values":value.0})
}

fn caller_inputs(
    target: HashOutput,
    entry_hash: HashOutput,
    enabled: bool,
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("target".into(), bytes32(target)),
        ("entryHash".into(), bytes32(entry_hash)),
        ("enabled".into(), json!(enabled)),
        ("opening".into(), json!("101")),
        ("argument".into(), json!("3")),
        ("expectedBalance".into(), json!("13")),
        ("expectedCount".into(), json!("1")),
        ("expectedEnabled".into(), json!(false)),
    ])
}

fn callee_inputs() -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("amount".into(), json!("3")),
        ("enabled".into(), json!(false)),
    ])
}

fn checked_call<'a>(
    execution: &'a noctium_runtime::Execution,
    circuit: &'a IrSource,
    state: ChargedState<noctium_runtime::Db>,
    address: ContractAddress,
    entry_point: EntryPointBuf,
    randomness: Fr,
) -> CheckedNativeCall<'a> {
    CheckedNativeCall {
        execution,
        circuit,
        initial_context: QueryContext::new(state, address),
        entry_point,
        communication_commitment_rand: randomness,
    }
}

#[test]
fn native_intent_assembles_a_call_forest_and_rejects_unmatched_claims() {
    let (caller_plan, caller_circuit) = caller_fixture();
    let (callee_plan, callee_circuit) = callee_fixture();
    let caller_address = ContractAddress(HashOutput([7; 32]));
    let callee_address = ContractAddress(HashOutput([42; 32]));
    let caller_state = create_state(
        &caller_plan,
        &BTreeMap::from([("marker".into(), json!("9"))]),
    )
    .unwrap();
    let callee_state = create_state(
        &callee_plan,
        &BTreeMap::from([
            ("balance".into(), json!("10")),
            ("count".into(), json!("0")),
        ]),
    )
    .unwrap();
    let callee_entry = EntryPointBuf::from(b"advance".to_vec());
    let callee_execution = prepare(
        &callee_plan,
        &callee_inputs(),
        &callee_state,
        &INITIAL_PARAMETERS,
        callee_address,
    )
    .unwrap();
    check(&callee_execution, &callee_circuit).unwrap();
    assert_eq!(
        callee_execution.returns_json(),
        BTreeMap::from([
            ("balanceValue".into(), json!("13")),
            ("countValue".into(), json!("1")),
            ("enabledValue".into(), json!(false)),
        ])
    );

    let entry_hash = callee_entry.ep_hash();
    let caller_execution = prepare(
        &caller_plan,
        &caller_inputs(callee_address.0, entry_hash, true),
        &caller_state,
        &INITIAL_PARAMETERS,
        caller_address,
    )
    .unwrap();
    assert_eq!(caller_execution.after.state, caller_state);
    assert_eq!(
        caller_execution.returns_json(),
        BTreeMap::from([("didClaim".into(), json!(true))])
    );
    let callee = || {
        checked_call(
            &callee_execution,
            &callee_circuit,
            callee_state.clone(),
            callee_address,
            callee_entry.clone(),
            Fr::from(101u64),
        )
    };
    let caller = |execution| {
        checked_call(
            execution,
            &caller_circuit,
            caller_state.clone(),
            caller_address,
            EntryPointBuf::from(b"claim".to_vec()),
            Fr::from(53u64),
        )
    };
    let assemble = |calls: &[CheckedNativeCall<'_>]| {
        assemble_checked_calls(calls, &INITIAL_PARAMETERS, 1_800_000_000, &mut OsRng)
    };
    let independent_address = ContractAddress(HashOutput([12; 32]));
    let independent_execution = prepare(
        &callee_plan,
        &callee_inputs(),
        &callee_state,
        &INITIAL_PARAMETERS,
        independent_address,
    )
    .unwrap();
    let independent = || {
        checked_call(
            &independent_execution,
            &callee_circuit,
            callee_state.clone(),
            independent_address,
            callee_entry.clone(),
            Fr::from(102u64),
        )
    };
    let intent = assemble(&[caller(&caller_execution), callee(), independent()]).unwrap();
    let assembled: Vec<_> = intent.calls().collect();
    assert_eq!(
        assembled.iter().map(|c| c.address).collect::<Vec<_>>(),
        [caller_address, callee_address, independent_address]
    );
    let ProofPreimageVersioned::V2(preimage) = &assembled[1].proof else {
        panic!("expected a V2 preimage");
    };
    assert_eq!(preimage.inputs, [Fr::from(3u64)]);
    assert_eq!(
        preimage.key_location.0,
        format!("{}:advance", hex::encode(callee_address.0.0))
    );
    assert!(assembled[0].calls(assembled[1]));
    assert!(!assembled[0].calls(assembled[2]));
    assert!(assemble(&[callee(), caller(&caller_execution)]).is_err());
    assert!(assemble(&[caller(&caller_execution)]).is_err());
    assert!(assemble(&[callee(), callee()]).is_err());

    let wrong_tuple = prepare(
        &caller_plan,
        &caller_inputs(HashOutput([43; 32]), entry_hash, true),
        &caller_state,
        &INITIAL_PARAMETERS,
        caller_address,
    )
    .unwrap();
    assert!(assemble(&[caller(&wrong_tuple), callee()]).is_err());

    let prepare_inactive = || {
        prepare(
            &caller_plan,
            &caller_inputs(callee_address.0, entry_hash, false),
            &caller_state,
            &INITIAL_PARAMETERS,
            caller_address,
        )
        .unwrap()
    };
    let inactive = prepare_inactive();
    check(&inactive, &caller_circuit).unwrap();
    assert!(inactive.after.effects.claimed_contract_calls.is_empty());
    assert_eq!(
        inactive.returns_json(),
        BTreeMap::from([("didClaim".into(), json!(false))])
    );
    assert_eq!(
        inactive
            .activity_schedule
            .iter()
            .filter_map(|skip| *skip)
            .collect::<Vec<_>>(),
        [1, 4, 1, 1, 11, 2, 2, 1, 1]
    );
    assert!(assemble(&[caller(&inactive)]).is_ok());

    let mut forged_inactive = prepare_inactive();
    forged_inactive.after.effects = caller_execution.after.effects.clone();
    let mut forged = caller(&forged_inactive);
    forged.initial_context.effects = caller_execution.after.effects.clone();
    assert!(assemble(&[forged, callee()]).is_err());
}

struct Operation {
    bundle: VerifiedBundle,
    plan: Plan,
    circuit: IrSource,
    entry: EntryPointBuf,
    deploy: ContractDeploy<Db>,
    srs: TrustedParameters,
}

impl Operation {
    fn load(role: &str, entry: &str, state: BTreeMap<String, Json>) -> Self {
        let root = PathBuf::from(env::var_os("NOCTIUM_COMPOSITION_BUNDLES").unwrap());
        let role_upper = role.to_ascii_uppercase();
        let pin = env::var(format!("NOCTIUM_COMPOSITION_{role_upper}_SHA256")).unwrap();
        let bundle = verify(&root.join(format!("{role}-bundle")), Some(&pin)).unwrap();
        let plan = serde_json::from_slice::<Plan>(bundle.file(Role::Plan).unwrap()).unwrap();
        let circuit = IrSource::load(bundle.file(Role::Circuit).unwrap()).unwrap();
        let verifier = serialize::tagged_deserialize::<VerifierKey>(
            &mut bundle.file(Role::VerifierKey).unwrap(),
        )
        .unwrap();
        let entry = EntryPointBuf(entry.as_bytes().to_vec());
        let mut contract = ContractState::<Db>::default();
        contract.data = create_state(&plan, &state).unwrap();
        contract.operations = contract
            .operations
            .insert(entry.clone(), ContractOperation::new(Some(verifier), None));
        let deploy = ContractDeploy::new(&mut OsRng, contract);
        let dir = PathBuf::from(env::var_os("NOCTIUM_COMPOSITION_SRS").unwrap());
        let srs = TrustedParameters::from_bytes(
            &fs::read(dir.join(format!("bls_midnight_2p{}", circuit.k()))).unwrap(),
            circuit.k(),
            &env::var(format!("NOCTIUM_COMPOSITION_{role_upper}_SRS_SHA256")).unwrap(),
        )
        .unwrap();
        Self {
            bundle,
            plan,
            circuit,
            entry,
            deploy,
            srs,
        }
    }

    fn proof_selection(&self) -> CompositionMaterial<'_> {
        CompositionMaterial {
            bundle: &self.bundle,
            parameters: &self.srs,
        }
    }
}

struct Pair {
    caller: Operation,
    callee: Operation,
}

impl Pair {
    fn load() -> Self {
        Self {
            caller: Operation::load(
                "caller",
                "claim",
                BTreeMap::from([("marker".into(), json!("9"))]),
            ),
            callee: Operation::load(
                "callee",
                "advance",
                BTreeMap::from([
                    ("balance".into(), json!("10")),
                    ("count".into(), json!("0")),
                ]),
            ),
        }
    }

    fn intent(
        &self,
        ledger: &LedgerState<Db>,
        ttl: u64,
    ) -> noctium_runtime::assembly::NativeIntent {
        let address = self.callee.deploy.address();
        let mut calls = Vec::new();
        let mut executions = Vec::new();
        for (operation, inputs, opening) in [
            (
                &self.caller,
                caller_inputs(address.0, self.callee.entry.ep_hash(), true),
                53u64,
            ),
            (&self.callee, callee_inputs(), 101u64),
        ] {
            let address = operation.deploy.address();
            let data = ledger.contract.get(&address).unwrap().data.clone();
            executions.push((
                operation,
                address,
                prepare(&operation.plan, &inputs, &data, &ledger.parameters, address).unwrap(),
                data,
                Fr::from(opening),
            ));
        }
        for (operation, address, execution, data, opening) in &executions {
            calls.push(checked_call(
                execution,
                &operation.circuit,
                data.clone(),
                *address,
                operation.entry.clone(),
                *opening,
            ));
        }
        assemble_checked_calls(&calls, &ledger.parameters, ttl, &mut OsRng).unwrap()
    }

    fn materials(&self) -> [CompositionMaterial<'_>; 2] {
        [self.caller.proof_selection(), self.callee.proof_selection()]
    }
}

#[test]
#[ignore = "requires independently pinned caller/callee bundles and their native SRS files"]
fn composed_intent_attaches_both_proofs_against_installed_keys() {
    use base_crypto::time::Timestamp;
    use futures::{executor::block_on, future::pending};
    use ledger::{
        structure::{LedgerParameters, StandardTransaction, Transaction},
        verify::WellFormedStrictness,
    };
    use noctium_runtime::proof::Error;
    use rand::{SeedableRng, rngs::StdRng};

    let pair = Pair::load();
    let mut ledger = LedgerState::<Db>::new("local");
    let mut ledger_parameters = serialize::tagged_deserialize::<LedgerParameters>(
        &mut pair.caller.bundle.file(Role::LedgerParameters).unwrap(),
    )
    .unwrap();
    ledger_parameters.fee_prices.overall_price =
        base_crypto::cost_model::FixedPoint::from_u64_div(42, 1);
    ledger.parameters = storage::arena::Sp::new(ledger_parameters);
    for operation in [&pair.caller, &pair.callee] {
        ledger.contract = ledger.contract.insert(
            operation.deploy.address(),
            operation.deploy.initial_state.clone(),
        );
    }
    let before = 1_800_000_000;
    let intent = pair.intent(&ledger, before + 30);

    let mut wrong_ledger = ledger.clone();
    let mut wrong_callee = pair.callee.deploy.initial_state.clone();
    let wrong_verifier = serialize::tagged_deserialize::<VerifierKey>(
        &mut pair.caller.bundle.file(Role::VerifierKey).unwrap(),
    )
    .unwrap();
    wrong_callee.operations = wrong_callee.operations.insert(
        pair.callee.entry.clone(),
        ContractOperation::new(Some(wrong_verifier), None),
    );
    wrong_ledger.contract = wrong_ledger
        .contract
        .insert(pair.callee.deploy.address(), wrong_callee);
    assert_eq!(
        PreparedComposition::from_intent(intent.clone(), &wrong_ledger, &pair.materials()).err(),
        Some(Error::BindingMismatch)
    );
    let prepared = PreparedComposition::from_intent(intent, &ledger, &pair.materials()).unwrap();
    let proved = block_on(prepared.prove_locally(OsRng, pending())).unwrap();
    let tx = Transaction::Standard(StandardTransaction {
        network_id: ledger.network_id.clone(),
        binding_randomness: proved.native().binding_commitment,
        intents: [(1, proved.native().clone())].into_iter().collect(),
        guaranteed_coins: None,
        fallible_coins: Default::default(),
    });
    let mut strictness = WellFormedStrictness::default();
    strictness.enforce_balancing = false;
    tx.seal(StdRng::from_entropy())
        .well_formed(&ledger, strictness, Timestamp::from_secs(before))
        .unwrap();
}

#[cfg(feature = "localnet")]
#[test]
#[ignore = "spends only the public development wallet on the explicit isolated Midnight localnet"]
fn composed_intent_finalizes_both_contract_states_on_localnet() {
    run_local_composition(false);
}

#[cfg(feature = "localnet")]
#[test]
#[ignore = "uses the isolated development wallet and the three registry operation bundles"]
fn registry_rotation_routes_two_finalized_calls_without_redeploying() {
    run_local_composition(true);
}

#[cfg(feature = "localnet")]
fn run_local_composition(registry: bool) {
    use base_crypto::time::Timestamp;
    use futures::{executor::block_on, future::pending};
    use noctium_runtime::{
        assembly::NativeIntent,
        client::{BoundTransaction, ChainAdapter, FinalizedReceipt, NetworkPolicy, Submission},
        funding::{CONTRACT_SEGMENT, FeePolicy, UnsealedTransaction},
        localnet::{DevelopmentFunding, ExplicitSeal, Node, ProofCache},
        proof::ProvedNativeIntent,
    };
    use rand::{SeedableRng, rngs::StdRng};
    use sha2::{Digest, Sha256};
    use std::time::{Duration, Instant};

    block_on(async {
        let policy = NetworkPolicy {
            network_id: "undeployed".into(),
            genesis: "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d".into(),
            spec_version: 2001100,
            transaction_version: 4,
            profile: noctium_runtime::profile::NAME.into(),
            max_dust: 10u128.pow(22),
        };
        let node = Node::connect(
            &env::var("NOCTIUM_COMPOSITION_NODE").unwrap(),
            policy.clone(),
            Duration::from_secs(30),
            64 * 1024 * 1024,
            100_000,
        )
        .unwrap();
        let mut seed = [0u8; 32];
        seed[31] = 1;
        node.attach_dust_seed(&seed).unwrap();
        let cache = ProofCache::new(
            PathBuf::from(env::var_os("NOCTIUM_COMPOSITION_SRS").unwrap()),
            "https://srs.midnight.network/".parse().unwrap(),
        )
        .unwrap();
        let dust = cache.dust().await.unwrap();
        let dust_srs = cache.parameters(dust.k()).await.unwrap();
        eprintln!("sync localnet");
        let snapshot = node.sync().unwrap();
        let submit = async |intent: &ProvedNativeIntent| -> FinalizedReceipt {
            let funding = DevelopmentFunding::new(
                &node,
                &dust,
                &dust_srs,
                FeePolicy {
                    max_dust: policy.max_dust,
                    margin_blocks: 3,
                    max_spends: 8,
                },
                StdRng::from_entropy(),
            );
            let signer = ExplicitSeal::new(
                |_: &UnsealedTransaction, actual: &NetworkPolicy| actual == &policy,
                StdRng::from_entropy(),
            );
            let bound = BoundTransaction::prepare(intent, policy.clone(), &node, &funding, &signer)
                .await
                .unwrap();
            eprintln!("submit {}", bound.transaction_id());
            assert!(!matches!(
                node.submit(&bound).await.unwrap(),
                Submission::Rejected
            ));
            let deadline = Instant::now() + Duration::from_secs(120);
            loop {
                if let Some(receipt) = node.finalized_receipt(&bound).unwrap() {
                    bound.check_receipt(&receipt).unwrap();
                    return receipt;
                }
                assert!(Instant::now() < deadline, "localnet finality timeout");
                std::thread::sleep(Duration::from_secs(2));
            }
        };

        let ttl = snapshot.block.tblock.to_secs() + 1800;
        let deploy = async |deployment: &ContractDeploy<Db>| {
            let intent = NativeIntent::empty(&mut OsRng, Timestamp::from_secs(ttl))
                .add_deploy(deployment.clone());
            let provider = builtin_zkir::LocalProvingProvider {
                rng: StdRng::from_entropy(),
                resolver: &dust,
                params: &dust_srs,
            };
            let (_, deployment) = intent
                .prove(
                    CONTRACT_SEGMENT,
                    provider,
                    &snapshot.state.parameters.cost_model.runtime_cost_model,
                )
                .await
                .unwrap();
            submit(&deployment).await
        };
        if registry {
            qualify_registry(&node, deploy, submit).await;
            return;
        }
        let pair = Pair::load();
        let mut deployment_receipts = Vec::new();
        for operation in [&pair.caller, &pair.callee] {
            deployment_receipts.push(deploy(&operation.deploy).await);
        }
        let live = node.sync().unwrap();
        let intent = pair.intent(&live.state, live.block.tblock.to_secs() + 1800);
        let prepared =
            PreparedComposition::from_intent(intent, &live.state, &pair.materials()).unwrap();
        let proved = prepared.prove_locally(OsRng, pending()).await.unwrap();
        let receipt = submit(proved.native()).await;
        assert_eq!(
            receipt.contract_address,
            hex::encode(pair.caller.deploy.address().0.0)
        );
        assert_eq!(
            receipt.contract_state,
            deployment_receipts[0].contract_state
        );
        let address = hex::encode(pair.callee.deploy.address().0.0);
        let bytes = &receipt.secondary_states[&address];
        let callee_state =
            serialize::tagged_deserialize::<ContractState<Db>>(&mut bytes.as_slice()).unwrap();
        let expected = create_state(
            &pair.callee.plan,
            &BTreeMap::from([
                ("balance".into(), json!("13")),
                ("count".into(), json!("1")),
            ]),
        )
        .unwrap();
        assert_eq!(callee_state.data, expected);
        eprintln!(
            "{}",
            json!({
                "genesis": receipt.chain.genesis,
                "profile": receipt.chain.profile,
                "height": receipt.height,
                "blockHash": receipt.block_hash,
                "transactionId": receipt.transaction_id,
                "intentId": receipt.intent_id,
                "extrinsicHash": receipt.extrinsic_hash,
                "extrinsicIndex": receipt.extrinsic_index,
                "deployments": deployment_receipts.iter().map(|r| json!({
                    "address": r.contract_address, "height": r.height, "transactionId":r.transaction_id,
                    "blockHash":r.block_hash,
                })).collect::<Vec<_>>(),
                "caller": {"address": receipt.contract_address, "stateSha256": hex::encode(Sha256::digest(&receipt.contract_state))},
                "callee": {"address": address, "balance": "13", "count": "1", "stateSha256": hex::encode(Sha256::digest(bytes))},
            })
        );
    });
}

#[cfg(feature = "localnet")]
async fn qualify_registry(
    node: &noctium_runtime::localnet::Node,
    deploy: impl AsyncFn(&ContractDeploy<Db>) -> noctium_runtime::client::FinalizedReceipt,
    submit: impl AsyncFn(
        &noctium_runtime::proof::ProvedNativeIntent,
    ) -> noctium_runtime::client::FinalizedReceipt,
) {
    use futures::future::pending;
    use noctium_runtime::field_decimal;
    use transient_crypto::hash::transient_hash;

    let callee = Operation::load(
        "callee",
        "store",
        BTreeMap::from([("stored".into(), json!("1"))]),
    );
    let first = callee.deploy.address();
    let replacement = ContractDeploy::new(&mut OsRng, callee.deploy.initial_state.clone());
    let second = replacement.address();
    assert_ne!(first, second);
    let authority = Fr::from(42u64);
    let config = |route: ContractAddress| {
        BTreeMap::from([
            ("route".into(), bytes32(route.0)),
            (
                "adminCommitment".into(),
                json!(field_decimal(transient_hash(&[authority]))),
            ),
        ])
    };
    let mut caller = Operation::load("caller", "claim", config(first));
    let rotate = Operation::load("rotate", "rotateRoute", config(first));
    let extra = rotate
        .deploy
        .initial_state
        .operations
        .get(&rotate.entry)
        .unwrap();
    let mut state = caller.deploy.initial_state.clone();
    state.operations = state
        .operations
        .insert(rotate.entry.clone(), (*extra).clone());
    caller.deploy = ContractDeploy::new(&mut OsRng, state);
    let caller_address = caller.deploy.address();
    let mut deployments = Vec::new();
    for deployment in [&callee.deploy, &replacement, &caller.deploy] {
        deployments.push(deploy(deployment).await);
    }

    let prove = async |intent, state: &LedgerState<Db>, selected: &[CompositionMaterial<'_>]| {
        let prepared = PreparedComposition::from_intent(intent, state, selected).unwrap();
        let proved = prepared.prove_locally(OsRng, pending()).await.unwrap();
        submit(proved.native()).await
    };
    let mut field_bytes = [0u8; 32];
    field_bytes[0] = 9;
    let callee_inputs = BTreeMap::from([
        ("aux".into(), json!("7")),
        ("flag".into(), json!(true)),
        ("score".into(), json!("200")),
        (
            "payload".into(),
            json!({"kind":"bytes", "values":(0..33).collect::<Vec<u8>>()}),
        ),
        ("empty".into(), json!({"kind":"bytes", "values":[]})),
        ("scalar".into(), json!({"kind":"jubjubScalar", "value":"1"})),
        (
            "point".into(),
            json!({"kind":"jubjubPoint", "x":"0", "y":"1"}),
        ),
        (
            "field".into(),
            json!({"kind":"foreign", "type":"Secp256k1Base", "bytes":field_bytes}),
        ),
    ]);
    let call = |ledger: &LedgerState<Db>,
                ttl,
                target: ContractAddress,
                role: EntryPointBuf,
                opening: u64| {
        let mut inputs = callee_inputs.clone();
        inputs.remove("aux");
        inputs.extend([
            ("opening".into(), json!(opening.to_string())),
            ("emptyAccepted".into(), json!(true)),
            ("expectedTail".into(), json!("32")),
            ("expectedScore".into(), json!("200")),
            ("expectedApproval".into(), json!(true)),
        ]);
        let caller_data = ledger.contract.get(&caller_address).unwrap().data.clone();
        let callee_data = ledger.contract.get(&target).unwrap().data.clone();
        let parent = prepare(
            &caller.plan,
            &inputs,
            &caller_data,
            &ledger.parameters,
            caller_address,
        )
        .unwrap();
        let child = prepare(
            &callee.plan,
            &callee_inputs,
            &callee_data,
            &ledger.parameters,
            target,
        )
        .unwrap();
        assemble_checked_calls(
            &[
                checked_call(
                    &parent,
                    &caller.circuit,
                    caller_data,
                    caller_address,
                    caller.entry.clone(),
                    Fr::from(opening + 1),
                ),
                checked_call(
                    &child,
                    &callee.circuit,
                    callee_data,
                    target,
                    role,
                    Fr::from(opening),
                ),
            ],
            &ledger.parameters,
            ttl,
            &mut OsRng,
        )
    };
    let selected = [caller.proof_selection(), callee.proof_selection()];
    let live = node.sync().unwrap();
    let ttl = live.block.tblock.to_secs() + 1800;
    assert!(
        call(
            &live.state,
            ttl,
            first,
            EntryPointBuf(b"other".to_vec()),
            101
        )
        .is_err()
    );
    let intent = call(&live.state, ttl, first, callee.entry.clone(), 101).unwrap();
    assert!(
        PreparedComposition::from_intent(
            intent.clone(),
            &live.state,
            &[caller.proof_selection(), rotate.proof_selection()]
        )
        .is_err()
    );
    let first_call = prove(intent, &live.state, &selected).await;

    let live = node.sync().unwrap();
    let ttl = live.block.tblock.to_secs() + 1800;
    let data = live
        .state
        .contract
        .get(&caller_address)
        .unwrap()
        .data
        .clone();
    let update = prepare(
        &rotate.plan,
        &BTreeMap::from([
            ("newTarget".into(), bytes32(second.0)),
            ("authority".into(), json!(field_decimal(authority))),
        ]),
        &data,
        &live.state.parameters,
        caller_address,
    )
    .unwrap();
    let intent = assemble_checked_calls(
        &[checked_call(
            &update,
            &rotate.circuit,
            data,
            caller_address,
            rotate.entry.clone(),
            Fr::from(99u64),
        )],
        &live.state.parameters,
        ttl,
        &mut OsRng,
    )
    .unwrap();
    let rotated = prove(intent, &live.state, &[rotate.proof_selection()]).await;
    let live = node.sync().unwrap();
    assert_eq!(
        live.state.contract.get(&caller_address).unwrap().data,
        create_state(&caller.plan, &config(second)).unwrap()
    );
    let ttl = live.block.tblock.to_secs() + 1800;
    assert!(call(&live.state, ttl, first, callee.entry.clone(), 103).is_err());
    let intent = call(&live.state, ttl, second, callee.entry.clone(), 103).unwrap();
    let second_call = prove(intent, &live.state, &selected).await;

    let verify = |receipt: &noctium_runtime::client::FinalizedReceipt, address: ContractAddress| {
        let key = hex::encode(address.0.0);
        assert_eq!(receipt.contract_address, hex::encode(caller_address.0.0));
        assert_eq!(receipt.secondary_states.len(), 1);
        let bytes = &receipt.secondary_states[&key];
        let state =
            serialize::tagged_deserialize::<ContractState<Db>>(&mut bytes.as_slice()).unwrap();
        assert_eq!(
            state.data,
            create_state(
                &callee.plan,
                &BTreeMap::from([("stored".into(), json!("200"))])
            )
            .unwrap()
        );
    };
    verify(&first_call, first);
    verify(&second_call, second);
    assert_eq!(first_call.contract_state, deployments[2].contract_state);
    assert_eq!(second_call.contract_state, rotated.contract_state);
    eprintln!(
        "{}",
        json!({
            "genesis": first_call.chain.genesis, "profile": first_call.chain.profile,
            "deployments": deployments.iter().map(|r| json!({"address":r.contract_address,"height":r.height,"blockHash":r.block_hash,"transactionId":r.transaction_id})).collect::<Vec<_>>(),
            "caller": hex::encode(caller_address.0.0),
            "firstCall": {"callee":hex::encode(first.0.0), "height":first_call.height,"blockHash":first_call.block_hash,"transactionId":first_call.transaction_id,"extrinsicHash":first_call.extrinsic_hash},
            "rotation": {"height":rotated.height,"blockHash":rotated.block_hash,"transactionId":rotated.transaction_id,"extrinsicHash":rotated.extrinsic_hash},
            "secondCall": {"callee":hex::encode(second.0.0),"height":second_call.height,"blockHash":second_call.block_hash,"transactionId":second_call.transaction_id,"extrinsicHash":second_call.extrinsic_hash},
            "rejected": ["wrong selector", "wrong callee bundle", "stale registry route"], "stored": "200"
        })
    );
}
