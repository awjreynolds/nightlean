//! Opt-in qualification of a hosted guarded call on the pinned development genesis.
#![cfg(all(feature = "localnet", feature = "zkir-321"))]

use anyhow::{Context, Result, anyhow, bail, ensure};
use futures::{executor::block_on, future::pending};
use ledger::structure::{ContractAction, ProofPreimageVersioned};
use noctium_runtime::{
    Db, Plan,
    artifacts::{self, ContractBundleSet, Role},
    client::{
        ChainAdapter, FundingAdapter, JournalStore, NetworkPolicy, RecoveryRecord, SigningAdapter,
        Snapshot,
    },
    create_state,
    funding::{DustMaterial, FeePolicy, UnsealedTransaction},
    host,
    localnet::{
        DEVELOPMENT_GENESIS, DevelopmentFunding, ExplicitSeal, Node, ProofCache,
        journal::DirectoryJournal,
    },
    proof::{
        CurrentStateContext, LocalProver, ProofRequest, ProofService, PublicProvedNativeIntent,
        ServiceError, TrustedParameters, WitnessContractTarget,
    },
    witness_execution::{
        GeneratedBinding, PrivateJson, WitnessClient, WitnessClientCommand as Command,
        WitnessClientReply as Reply, WitnessExecution,
    },
    zkir::IrSource,
};
use onchain_runtime::{
    ops::Op,
    state::{ChargedState, ContractState},
};
use rand::{
    RngCore, SeedableRng,
    rngs::{OsRng, StdRng},
};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env,
    path::Path,
    thread::sleep,
    time::{Duration, Instant},
};
use transient_crypto::{
    curve::Fr,
    proofs::{ProvingKeyMaterial, Zkir},
};

const OPERATION: &str = "noctium.derive.v1";
const KEY: &str = "ledger/last";

fn decode<T: serialize::Deserializable + serialize::Tagged>(bytes: &[u8]) -> Result<T> {
    let mut input = bytes;
    let value = serialize::tagged_deserialize(&mut input)?;
    ensure!(input.is_empty(), "trailing native bytes");
    Ok(value)
}

fn attempt_id() -> String {
    let mut bytes = [0; 32];
    OsRng.fill_bytes(&mut bytes);
    hex::encode(bytes)
}

struct Host<'a> {
    node: &'a Node,
    policy: &'a NetworkPolicy,
    dust: &'a DustMaterial,
    dust_parameters: &'a TrustedParameters,
    store: &'a DirectoryJournal,
    namespace: &'a str,
}

impl Host<'_> {
    fn private_value(&self) -> Result<Option<Json>> {
        self.store
            .private_value(self.namespace, KEY)
            .map_err(|_| anyhow!("fixture private value unavailable"))
    }

    fn context(&self, attempt: &str, provider: bool) -> Result<host::Context> {
        let revision = self
            .store
            .revision(self.namespace)
            .map_err(|_| anyhow!("fixture private revision unavailable"))?;
        let mut context: host::Context = serde_json::from_value(json!({
            "protocolVersion": 1, "namespace": self.namespace, "baseRevision": revision,
            "attemptId": attempt, "providers": [], "operations": [], "commitCapability": "commit",
            "capabilities": [
                {"id": "private", "namespace": self.namespace, "keyPrefix": "ledger/", "operations": [host::STAGE]},
                {"id": "commit", "namespace": self.namespace, "keyPrefix": "ledger/", "operations": [host::CAS]}
            ]
        }))?;
        if provider {
            context.capabilities.push(host::Capability {
                id: "derive".into(),
                namespace: self.namespace.into(),
                key_prefix: "lookup/".into(),
                operations: vec![OPERATION.into()],
            });
            context.operations.push(host::Operation {
                operation: OPERATION.into(),
                argument_schema: BTreeMap::from([("balance".into(), "Native".into())]),
                result_schema: "Native".into(),
            });
            context.providers.push(host::Provider {
                input: "derive".into(),
                operation: OPERATION.into(),
                capability: "derive".into(),
                arguments: BTreeMap::new(),
            });
        }
        Ok(context)
    }

    async fn finalize(
        &self,
        mut client: WitnessClient,
        expected: &ChargedState<Db>,
        staged: bool,
    ) -> Result<(CurrentStateContext, Json)> {
        let previous = self.private_value()?;
        let mut snapshot = None;
        let mut revision = None;
        let deadline = Instant::now() + Duration::from_secs(90);
        client.command(Command::Prepare)?;
        loop {
            ensure!(Instant::now() < deadline, "development client timed out");
            let status = client.poll()?;
            if let Some(request) = client.request()? {
                let payload = || {
                    request
                        .private_payload()
                        .context("host request has no payload")
                };
                let reply = match request.metadata["operation"].as_str().unwrap_or_default() {
                    "chain.snapshot.v1" => {
                        let live = self.node.sync()?;
                        snapshot = Some(Snapshot {
                            chain: live.chain.clone(),
                            finalized_hash: live.finalized_hash.clone(),
                            height: live.height,
                            state: live.state.clone(),
                            block: live.block.clone(),
                        });
                        Reply::Snapshot(live)
                    }
                    "funding.native.v1" => Reply::Funded(
                        DevelopmentFunding::new(
                            self.node,
                            self.dust,
                            self.dust_parameters,
                            FeePolicy {
                                max_dust: self.policy.max_dust,
                                margin_blocks: 3,
                                max_spends: 8,
                            },
                            StdRng::from_entropy(),
                        )
                        .fund(
                            &decode(payload()?)?,
                            snapshot.as_ref().context("funding snapshot")?,
                            self.policy,
                        )
                        .await
                        .map_err(|_| anyhow!("native funding failed"))?,
                    ),
                    "approval.sign.v1" => Reply::Signed(
                        ExplicitSeal::new(
                            |_: &UnsealedTransaction, policy: &NetworkPolicy| policy == self.policy,
                            StdRng::from_entropy(),
                        )
                        .approve_and_sign(
                            &decode(payload()?)?,
                            snapshot.as_ref().context("signing snapshot")?,
                            self.policy,
                        )
                        .await
                        .map_err(|_| anyhow!("native signing failed"))?,
                    ),
                    "chain.submit.v1" => Reply::Submitted(
                        self.node
                            .submit(request.transaction().context("submit binding")?)
                            .await
                            .map_err(|_| anyhow!("native submission failed"))?,
                    ),
                    "chain.observe.v1" => Reply::Observed(
                        self.node
                            .observe(request.transaction().context("observe binding")?)
                            .await
                            .map_err(|_| anyhow!("native receipt observation failed"))?,
                    ),
                    "journal.persist.v1" => {
                        let record = serde_json::from_slice(payload()?)?;
                        let acknowledgement = self
                            .store
                            .persist(&record, revision)
                            .await
                            .map_err(|_| anyhow!("journal persist failed"))?;
                        revision = Some(acknowledgement.revision);
                        Reply::Persisted(acknowledgement)
                    }
                    "private_state.compare_exchange.v1" => {
                        let record: RecoveryRecord = serde_json::from_slice(payload()?)?;
                        let journal: Json = serde_json::from_slice(record.journal_bytes())?;
                        let writes = journal["writes"].as_object().context("journal writes")?;
                        ensure!(
                            self.private_value()? == previous,
                            "private value changed before CAS"
                        );
                        if staged {
                            ensure!(
                                writes.len() == 1 && writes[KEY]["value"] == "7",
                                "wrong active private write"
                            );
                        } else {
                            ensure!(writes.is_empty(), "inactive source staged a private write");
                        }
                        Reply::Cas(
                            self.store
                                .compare_exchange(&record)
                                .await
                                .map_err(|_| anyhow!("private CAS failed"))?,
                        )
                    }
                    _ => bail!("unexpected native service request"),
                };
                client.complete(request.id, reply)?;
                continue;
            }
            ensure!(
                status["status"] != "failed" && status["status"] != "step_error",
                "native client failed: {status}"
            );
            match status["phase"].as_str().unwrap_or_default() {
                "Prepared" => {
                    client.command(Command::Submit)?;
                }
                "Submitted" | "Uncertain" => {
                    sleep(Duration::from_millis(500));
                    client.command(Command::Observe)?;
                }
                "AwaitingCas" => {
                    let bytes = client.receipt_state()?;
                    let accepted: ContractState<Db> = decode(&bytes)?;
                    ensure!(
                        accepted.data.get_ref() == expected.get_ref(),
                        "wrong finalized public state"
                    );
                    let address = status["contractAddress"]
                        .as_str()
                        .context("finalized address")?;
                    ensure!(
                        self.node.finalized_contract_state(address)?.bytes == bytes,
                        "finalized snapshot differs from receipt bytes"
                    );
                    ensure!(
                        self.private_value()? == previous,
                        "private value changed before finality"
                    );
                    client.command(Command::Commit)?;
                }
                "Committed" => {
                    ensure!(
                        status["privateAcknowledged"] == true && status["privateCommitted"] == true,
                        "private journal commit failed"
                    );
                    let current = self.private_value()?;
                    if staged {
                        ensure!(
                            current.as_ref().is_some_and(|value| value["value"] == "7"),
                            "active write did not commit"
                        );
                    } else {
                        ensure!(
                            current == previous,
                            "inactive invocation changed private state"
                        );
                    }
                    return Ok((client.current_state_context()?, status["receipt"].clone()));
                }
                _ => bail!("unexpected native client status: {status}"),
            }
        }
    }
}

fn run_source(
    execution: &mut WitnessExecution,
    attempt: &str,
    expected_calls: usize,
) -> Result<PrivateJson> {
    let mut provider_calls = 0;
    loop {
        let status = execution.advance()?;
        if status["status"] != "need_host" {
            ensure!(provider_calls == expected_calls, "wrong callback count");
            return Ok(status);
        }
        provider_calls += 1;
        ensure!(
            provider_calls <= expected_calls,
            "inactive source requested a provider"
        );
        ensure!(
            execution.private_request()?["arguments"]["balance"] == "3",
            "provider did not receive the prior ledger read"
        );
        execution.resume_typed(GeneratedBinding::reply(
            &status["request"],
            attempt,
            ("derive", OPERATION, "derive", "Native"),
            json!("7"),
        )?)?;
    }
}

struct CheckTranscript<'a>(&'a IrSource);

impl ProofService for CheckTranscript<'_> {
    async fn prove(&self, request: ProofRequest<'_>) -> Result<Vec<u8>, ServiceError> {
        let payload = request.private_wire_payload().map_err(|_| ServiceError)?;
        let (preimage, _, _): (
            ProofPreimageVersioned,
            Option<ProvingKeyMaterial>,
            Option<Fr>,
        ) = decode(&payload).map_err(|_| ServiceError)?;
        let ProofPreimageVersioned::V2(preimage) = preimage else {
            return Err(ServiceError);
        };
        let mut changed = (*preimage).clone();
        let first = changed
            .public_transcript_inputs
            .first_mut()
            .ok_or(ServiceError)?;
        *first = *first + Fr::from(1u64);
        assert!(
            changed.check(self.0).is_err(),
            "changed transcript passed the checker"
        );
        request.prove_locally(StdRng::from_entropy()).await
    }
}

fn check_order(bytes: &[u8], order: &str) -> Result<()> {
    let intent: PublicProvedNativeIntent = decode(bytes)?;
    let Some(ContractAction::Call(call)) = intent.actions.iter_deref().next() else {
        bail!("call proof omitted native action");
    };
    let actual: String = call
        .guaranteed_transcript
        .iter()
        .chain(call.fallible_transcript.iter())
        .flat_map(|transcript| transcript.program.iter_deref())
        .skip_while(|op| !matches!(op, Op::Ins { .. }))
        .filter_map(|op| match op {
            Op::Ins { .. } => Some('W'),
            Op::Popeq { .. } => Some('R'),
            _ => None,
        })
        .collect();
    ensure!(
        actual == order,
        "native read/write order {actual}, expected {order}"
    );
    Ok(())
}

async fn run() -> Result<Json> {
    let setting = |name| env::var(name).with_context(|| format!("missing {name}"));
    let pin = setting("NOCTIUM_GUARD_MANIFEST_SHA256")?;
    let bundle = artifacts::verify(Path::new(&setting("NOCTIUM_GUARD_BUNDLE")?), Some(&pin))?;
    let plan: Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
    let circuit_bytes = bundle.file(Role::Circuit)?;
    let circuit = IrSource::load(circuit_bytes)?;
    let circuit_sha256 = artifacts::digest(circuit_bytes);
    let impact_sha256 = artifacts::digest(bundle.file(Role::Plan)?);
    let cache = ProofCache::new(
        setting("NOCTIUM_GUARD_PARAMETER_CACHE")?.into(),
        "https://srs.midnight.network/".parse()?,
    )?;
    let policy = NetworkPolicy {
        network_id: "undeployed".into(),
        genesis: DEVELOPMENT_GENESIS.into(),
        spec_version: 2_001_100,
        transaction_version: 4,
        profile: noctium_runtime::profile::NAME.into(),
        max_dust: 10u128.pow(22),
    };
    let node = Node::connect(
        &setting("NOCTIUM_GUARD_NODE")?,
        policy.clone(),
        Duration::from_secs(30),
        64 * 1024 * 1024,
        100_000,
    )?;
    let mut seed = [0u8; 32];
    seed[31] = 1;
    node.attach_dust_seed(&seed)?;
    let dust = cache.dust().await?;
    let dust_parameters = cache.parameters(dust.k()).await?;
    let parameters = cache.parameters(circuit.k()).await?;
    let ttl = node.sync()?.block.tblock.to_secs() + 1_800;
    let target = WitnessContractTarget::from_state_config(
        ContractBundleSet::new(vec![bundle])?,
        br#"{"state":{"balance":"3","mark":"0"}}"#,
        ttl,
        &mut OsRng,
    )?;
    let namespace = format!("guarded-ledger-{}", target.contract_address());
    let store = DirectoryJournal::new(
        Path::new(&setting("NOCTIUM_GUARD_JOURNAL")?),
        Duration::from_secs(2),
    )
    .map_err(|_| anyhow!("fixture journal unavailable"))?;
    let host = Host {
        node: &node,
        policy: &policy,
        dust: &dust,
        dust_parameters: &dust_parameters,
        store: &store,
        namespace: &namespace,
    };
    let descriptor = serde_json::to_vec(&json!({
        "abiVersion": 1,
        "policy": {"networkId": policy.network_id, "genesis": policy.genesis, "specVersion": policy.spec_version,
                   "transactionVersion": policy.transaction_version, "profile": policy.profile,
                   "maxDust": policy.max_dust.to_string()},
        "capabilities": {"chain":"chain", "funding":"wallet", "signing":"signer", "journal":"store"}
    }))?;
    let expected_state = |balance: &str, mark: &str| {
        create_state(
            &plan,
            &BTreeMap::from([
                ("balance".into(), json!(balance)),
                ("mark".into(), json!(mark)),
            ]),
        )
    };
    let setup = serde_json::to_vec(
        &json!({"hostContext":host.context(&attempt_id(), false)?,"stages":[]}),
    )?;
    let deployment = target.start_deployment_client("advance", &descriptor, &setup)?;
    let (initial, deployed) = host
        .finalize(deployment, &expected_state("3", "0")?, false)
        .await?;
    let mut current = Some(initial);
    let operation = target.operation("advance", &parameters, ttl)?;
    let inputs = |outer, inner, bound, expected| {
        BTreeMap::from([
            ("outer".into(), json!(outer)),
            ("inner".into(), json!(inner)),
            ("bound".into(), json!(bound)),
            ("expected".into(), json!(expected)),
        ])
    };
    for (bound, expected, calls) in [("8", "10", 0), ("7", "99", 1)] {
        let attempt = attempt_id();
        let mut execution = WitnessExecution::begin_contract_operation(
            &operation,
            &mut current,
            inputs(true, true, bound, expected),
            host.context(&attempt, true)?,
            &parameters,
        )?;
        let result = run_source(&mut execution, &attempt, calls)?;
        ensure!(
            result["status"] == "failed" && result["error"]["code"] == "execution_rejected",
            "active invalid input was not rejected"
        );
        ensure!(
            execution.prepare_contract_proof(&mut OsRng).is_err(),
            "failed source invocation prepared a proof"
        );
        current = Some(execution.cancel_contract_operation()?.1);
        ensure!(
            host.private_value()?.is_none(),
            "failed invocation committed a private value"
        );
    }

    let mut receipts = vec![deployed];
    for (outer, inner, bound, expected, mark, calls, order) in [
        (true, true, "7", "10", "1", 1, "WRWRR"),
        (true, false, "8", "999", "2", 0, "WR"),
        (false, true, "8", "999", "3", 0, "WR"),
    ] {
        let attempt = attempt_id();
        let mut execution = WitnessExecution::begin_contract_operation(
            &operation,
            &mut current,
            inputs(outer, inner, bound, expected),
            host.context(&attempt, true)?,
            &parameters,
        )?;
        let result = run_source(&mut execution, &attempt, calls)?;
        ensure!(
            result["status"] == "completed" && result["result"] == "10",
            "source return did not observe the finalized balance"
        );
        let mut proof = execution.prepare_contract_proof(&mut OsRng)?;
        let mut proved = if calls == 1 {
            proof
                .prove(
                    &CheckTranscript(&circuit),
                    &parameters,
                    1_048_576,
                    pending(),
                )
                .await?
        } else {
            proof
                .prove(
                    &LocalProver::new(StdRng::from_entropy()),
                    &parameters,
                    1_048_576,
                    pending(),
                )
                .await?
        };
        ensure!(
            proved.contract_address() == target.contract_address(),
            "call changed targets"
        );
        check_order(&proved.public_serialized()?, order)?;
        let (updated, mut receipt) = host
            .finalize(
                proved.start_call_client(&descriptor)?,
                &expected_state("10", mark)?,
                calls == 1,
            )
            .await?;
        current = Some(updated);
        receipt["providerCalls"] = json!(calls);
        receipts.push(receipt);
    }
    Ok(json!({
        "genesis": policy.genesis, "profile": policy.profile, "manifestSha256": pin,
        "circuitSha256": circuit_sha256, "impactSha256": impact_sha256,
        "parametersSha256": parameters.sha256(), "receipts": receipts,
        "checks": {"activeCastRejected": true, "activeAssertionRejected": true, "changedTranscriptRejected": true}
    }))
}

#[test]
#[ignore = "requires the authenticated guarded witness bundle and a funded Ledger 9 development node"]
fn nested_guarded_witness_finalizes_on_ledger_9() {
    println!(
        "{}",
        block_on(run()).expect("guarded witness qualification")
    );
}
