//! Opt-in native development fixture. Wallet secrets and amounts are public test data.
#[path = "confidential_token_localnet/token.rs"]
mod token;

use anyhow::{Context, Result, anyhow, bail, ensure};
use futures::{executor::block_on, future::pending};
use noctium_runtime::{
    Db, Plan,
    artifacts::{self, ContractBundleSet, Role},
    client::{
        ChainAdapter, FundingAdapter, JournalStore, NetworkPolicy, RecoveryRecord, SigningAdapter,
        Snapshot, SubmissionAttempt,
    },
    funding::{DustMaterial, FeePolicy, UnsealedTransaction},
    host,
    localnet::{DevelopmentFunding, ExplicitSeal, Node, ProofCache, journal::DirectoryJournal},
    proof::{CurrentStateContext, LocalProver, TrustedParameters, WitnessContractTarget},
    witness_execution::{
        WitnessClient, WitnessClientCommand as Command, WitnessClientReply as Reply,
        WitnessExecution,
    },
    zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, ContractState};
use rand::{
    RngCore, SeedableRng,
    rngs::{OsRng, StdRng},
};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    io::Read,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};
use transient_crypto::proofs::Zkir;
use zeroize::Zeroizing;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Configuration {
    endpoint: String,
    policy: NetworkPolicy,
    bundle_index: PathBuf,
    bundle_index_sha256: String,
    parameter_cache: PathBuf,
    parameter_source: String,
    journal_directory: PathBuf,
    approve_local_development: bool,
    wait_seconds: u64,
    deployment_attempt: Option<String>,
    resume_attempt: Option<String>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct BundleLocation {
    name: String,
    directory: PathBuf,
    manifest_sha256: String,
}

fn read(path: &Path, limit: usize) -> Result<Zeroizing<Vec<u8>>> {
    let mut bytes = Zeroizing::new(Vec::new());
    std::fs::File::open(path)?
        .take(limit as u64 + 1)
        .read_to_end(&mut bytes)?;
    ensure!(bytes.len() <= limit, "host file exceeds byte limit");
    Ok(bytes)
}

fn attempt_id() -> String {
    let mut bytes = [0; 32];
    OsRng.fill_bytes(&mut bytes);
    hex::encode(bytes)
}

struct Host {
    plan: Plan,
    state: ChargedState<Db>,
    node: Node,
    cache: ProofCache,
    dust: DustMaterial,
    dust_parameters: TrustedParameters,
    store: DirectoryJournal,
    policy: NetworkPolicy,
    descriptor: Vec<u8>,
    target: WitnessContractTarget,
    current_state: Option<CurrentStateContext>,
    witness_plans: BTreeMap<String, Json>,
    degrees: BTreeMap<String, u8>,
    namespace: String,
    wait: Duration,
    ready: bool,
}

impl Host {
    fn context(&self, plan: &Json, attempt: &str) -> Result<host::Context> {
        let revision = self
            .store
            .revision(&self.namespace)
            .map_err(|_| anyhow!("private revision unavailable"))?;
        token::context(plan, attempt, &self.namespace, &revision)
    }

    fn setup(&self, attempt: &str) -> Result<Vec<u8>> {
        Ok(serde_json::to_vec(
            &json!({"hostContext":self.context(&json!({"witnesses":[]}),attempt)?,"stages":[]}),
        )?)
    }

    async fn invoke(
        &mut self,
        name: &str,
        inputs: BTreeMap<String, Json>,
        wallet: Option<&token::Wallet>,
    ) -> Result<()> {
        println!("{}", json!({"stage":"prepare","entrypoint":name}));
        let parameters = self
            .cache
            .parameters(*self.degrees.get(name).context("unknown operation")?)
            .await?;
        let live = self.node.sync()?;
        let operation =
            self.target
                .operation(name, &parameters, live.block.tblock.to_secs() + 1800)?;
        let attempt = attempt_id();
        let prover = LocalProver::new(StdRng::from_entropy());
        let client = if let Some(plan) = self.witness_plans.get(name) {
            let context = self.context(plan, &attempt)?;
            let mut execution = WitnessExecution::begin_contract_operation(
                &operation,
                &mut self.current_state,
                inputs,
                context,
                &parameters,
            )?;
            token::complete_source(
                &mut execution,
                &attempt,
                wallet.context("source operation requires fixture wallet")?,
            )?;
            let mut prepared = execution.prepare_contract_proof(&mut OsRng)?;
            println!(
                "{}",
                json!({"stage":"prove","entrypoint":name,"k":parameters.k()})
            );
            let mut proved = prepared
                .prove(&prover, &parameters, 1_048_576, pending())
                .await?;
            proved.start_call_client(&self.descriptor)?
        } else {
            let prepared =
                operation.prepare_call(&mut self.current_state, &parameters, inputs, &mut OsRng)?;
            println!(
                "{}",
                json!({"stage":"prove","entrypoint":name,"k":parameters.k()})
            );
            let mut proved = Some(
                prepared
                    .prove(&prover, &parameters, 1_048_576, pending())
                    .await?,
            );
            self.target.start_call_client(
                &operation,
                &mut proved,
                &self.descriptor,
                &self.setup(&attempt)?,
            )?
        };
        self.finish(client).await?;
        Ok(())
    }

    async fn finish(&mut self, mut client: WitnessClient) -> Result<()> {
        if client.status()["busy"] != true {
            client.command(Command::Prepare)?;
        }
        let mut snapshot = None;
        let mut revision = None;
        let deadline = Instant::now() + self.wait;
        loop {
            let status = client.poll()?;
            if let Some(request) = client.request()? {
                let payload = || {
                    request
                        .private_payload()
                        .context("private service payload missing")
                };
                let reply = match request.metadata["operation"]
                    .as_str()
                    .context("missing service operation")?
                {
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
                    "funding.native.v1" => {
                        let intent = decode(payload()?)?;
                        let funding = DevelopmentFunding::new(
                            &self.node,
                            &self.dust,
                            &self.dust_parameters,
                            FeePolicy {
                                max_dust: self.policy.max_dust,
                                margin_blocks: 3,
                                max_spends: 8,
                            },
                            StdRng::from_entropy(),
                        );
                        Reply::Funded(
                            funding
                                .fund(
                                    &intent,
                                    snapshot.as_ref().context("missing funding snapshot")?,
                                    &self.policy,
                                )
                                .await
                                .map_err(|_| anyhow!("native funding failed"))?,
                        )
                    }
                    "approval.sign.v1" => {
                        let transaction: UnsealedTransaction = decode(payload()?)?;
                        let signer = ExplicitSeal::new(
                            |_: &UnsealedTransaction, p: &NetworkPolicy| *p == self.policy,
                            StdRng::from_entropy(),
                        );
                        Reply::Signed(
                            signer
                                .approve_and_sign(
                                    &transaction,
                                    snapshot.as_ref().context("missing signing snapshot")?,
                                    &self.policy,
                                )
                                .await
                                .map_err(|_| anyhow!("native signing failed"))?,
                        )
                    }
                    "chain.submit.v1" => Reply::Submitted(
                        self.node
                            .submit(request.transaction().context("missing submit binding")?)
                            .await
                            .map_err(|_| anyhow!("native submission unresolved"))?,
                    ),
                    "chain.observe.v1" => Reply::Observed(
                        self.node
                            .observe(request.transaction().context("missing observe binding")?)
                            .await
                            .map_err(|_| anyhow!("native receipt observation failed"))?,
                    ),
                    "journal.persist.v1" => {
                        let record: RecoveryRecord = serde_json::from_slice(payload()?)?;
                        let acknowledgement = self
                            .store
                            .persist(&record, revision)
                            .await
                            .map_err(|_| anyhow!("journal persistence failed"))?;
                        revision = Some(acknowledgement.revision);
                        Reply::Persisted(acknowledgement)
                    }
                    "journal.load.v1" => {
                        let id = std::str::from_utf8(payload()?)?;
                        let loaded = self
                            .store
                            .load(id)
                            .await
                            .map_err(|_| anyhow!("journal recovery failed"))?;
                        revision = Some(loaded.revision);
                        Reply::Loaded(loaded)
                    }
                    "private_state.compare_exchange.v1" => {
                        let record: RecoveryRecord = serde_json::from_slice(payload()?)?;
                        Reply::Cas(
                            self.store
                                .compare_exchange(&record)
                                .await
                                .map_err(|_| anyhow!("private commit failed"))?,
                        )
                    }
                    other => bail!("unsupported native host service: {other}"),
                };
                client.complete(request.id, reply)?;
                continue;
            }
            ensure!(
                status["status"] != "failed" && status["status"] != "step_error",
                "native client step failed: {status}"
            );
            if status["busy"] == true {
                continue;
            }
            match status["phase"].as_str().unwrap_or("") {
                "Prepared" => {
                    client.command(Command::Submit)?;
                }
                "Submitted" | "Uncertain" => {
                    if Instant::now() >= deadline {
                        client.command(Command::Deadline)?;
                        bail!(
                            "submission unresolved, preserve and recover the same durable attempt"
                        );
                    }
                    std::thread::sleep(Duration::from_millis(500));
                    client.command(Command::Observe)?;
                }
                "AwaitingCas" => {
                    client.command(Command::Commit)?;
                }
                "Committed" => {
                    if status["receipt"].is_null() {
                        client.command(Command::Observe)?;
                        continue;
                    }
                    if status["privateAcknowledged"] != true {
                        client.command(Command::Commit)?;
                        continue;
                    }
                    self.current_state = Some(client.current_state_context()?);
                    let accepted: ContractState<Db> = decode(&client.receipt_state()?)?;
                    self.ready = accepted.operations.size() == 16
                        && accepted.maintenance_authority.committee.is_empty()
                        && accepted.maintenance_authority.threshold == 1;
                    self.state = accepted.data.clone();
                    println!(
                        "{}",
                        json!({"stage":"finalized","receipt":status["receipt"],"privateCommitted":status["privateCommitted"]})
                    );
                    return Ok(());
                }
                "Rejected" | "Failed" | "Conflicted" | "Cancelled" => {
                    bail!("native lifecycle terminated: {}", status["phase"])
                }
                _ => bail!("native client stopped without a lifecycle phase: {status}"),
            }
        }
    }
}

fn decode<T: serialize::Deserializable + serialize::Tagged>(bytes: &[u8]) -> Result<T> {
    let mut input = bytes;
    let value = serialize::tagged_deserialize(&mut input)?;
    ensure!(input.is_empty(), "trailing native bytes");
    Ok(value)
}

async fn run(configuration: Configuration) -> Result<()> {
    ensure!(
        configuration.deployment_attempt.is_some() == configuration.resume_attempt.is_some(),
        "recovery requires both deploymentAttempt and resumeAttempt"
    );
    ensure!(
        configuration.approve_local_development,
        "explicit local development approval required"
    );
    ensure!(
        (1..=300).contains(&configuration.wait_seconds),
        "invalid observation deadline"
    );
    ensure!(
        configuration.policy.genesis
            == "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d",
        "public fixture requires isolated development genesis"
    );
    let index = read(&configuration.bundle_index, 32_768)?;
    ensure!(
        artifacts::digest(&index) == configuration.bundle_index_sha256,
        "bundle index digest mismatch"
    );
    let locations: Vec<BundleLocation> = serde_json::from_slice(&index)?;
    ensure!(
        locations.len() == 16,
        "token fixture requires all sixteen operations"
    );
    let mut bundles = Vec::new();
    let mut witness_plans = BTreeMap::new();
    let mut degrees = BTreeMap::new();
    let mut plan = None;
    for location in locations {
        let bundle = artifacts::verify(&location.directory, Some(&location.manifest_sha256))?;
        let selected: Plan = serde_json::from_slice(bundle.file(Role::Plan)?)?;
        ensure!(
            selected.entrypoint == location.name && !degrees.contains_key(&location.name),
            "operation index mismatch"
        );
        degrees.insert(
            location.name.clone(),
            IrSource::load(bundle.file(Role::Circuit)?)?.k(),
        );
        if let Ok(bytes) = bundle.file(Role::WitnessControl) {
            witness_plans.insert(location.name.clone(), serde_json::from_slice(bytes)?);
        }
        if plan.is_none() {
            plan = Some(selected);
        }
        bundles.push(bundle);
    }
    println!(
        "{}",
        json!({"stage":"authenticated","operations":bundles.len()})
    );
    let node = Node::connect(
        &configuration.endpoint,
        configuration.policy.clone(),
        Duration::from_secs(30),
        64 * 1024 * 1024,
        100_000,
    )?;
    let mut seed = Zeroizing::new([0; 32]);
    seed[31] = 1;
    node.attach_dust_seed(&*seed)?;
    drop(seed);
    let snapshot = node.sync()?;
    println!("{}", json!({"stage":"synced","height":snapshot.height}));
    let cache = ProofCache::new(
        configuration.parameter_cache,
        reqwest::Url::parse(&configuration.parameter_source)?,
    )?;
    let dust = cache.dust().await?;
    let dust_parameters = cache.parameters(dust.k()).await?;
    let constructor = BTreeMap::from([
        ("name_".into(), json!("Noctium Token")),
        ("symbol_".into(), json!("NOC")),
        ("decimals_".into(), json!("6")),
    ]);
    let plan = plan.context("missing operation plan")?;
    let state = noctium_runtime::construct_state(&plan, &constructor)?;
    let bootstrap_signer = base_crypto::schnorr::SigningKey::from_bytes(&[29; 32])
        .map_err(|_| anyhow!("invalid public fixture maintenance key"))?;
    let initial_operations: Vec<_> = degrees.keys().take(8).cloned().collect();
    let remaining_operations: Vec<_> = degrees.keys().skip(8).cloned().collect();
    let mut target = WitnessContractTarget::from_staged_state_config(
        ContractBundleSet::new(bundles)?,
        &serde_json::to_vec(&json!({"state":constructor}))?,
        &initial_operations,
        bootstrap_signer.verifying_key(),
        snapshot.block.tblock.to_secs() + 1800,
        &mut OsRng,
    )?;
    let store = DirectoryJournal::new(&configuration.journal_directory, Duration::from_secs(2))
        .map_err(|_| anyhow!("journal unavailable"))?;
    if let Some(id) = &configuration.deployment_attempt {
        let attempt = SubmissionAttempt::recover(&store, id).await?;
        target = target.restore_deployment(
            &attempt,
            snapshot.block.tblock.to_secs() + 1800,
            &mut OsRng,
        )?;
    }
    let namespace = format!("noctium-token-{}", target.contract_address());
    let policy = configuration.policy;
    let descriptor = serde_json::to_vec(
        &json!({"abiVersion":1,"policy":{"networkId":policy.network_id,"genesis":policy.genesis,"specVersion":policy.spec_version,"transactionVersion":policy.transaction_version,"profile":policy.profile,"maxDust":policy.max_dust.to_string()},"capabilities":{"chain":"chain","funding":"wallet","signing":"signer","journal":"store"}}),
    )?;
    let mut host = Host {
        plan,
        state,
        node,
        cache,
        dust,
        dust_parameters,
        store,
        policy,
        descriptor,
        target,
        current_state: None,
        witness_plans,
        degrees,
        namespace,
        wait: Duration::from_secs(configuration.wait_seconds),
        ready: false,
    };
    if let Some(id) = configuration.resume_attempt {
        let attempt = SubmissionAttempt::recover(&host.store, &id).await?;
        let journal: Json = serde_json::from_slice(attempt.record().journal_bytes())?;
        let entry = journal["entrypoint"]
            .as_str()
            .context("recovery entrypoint missing")?;
        let plan = host
            .witness_plans
            .get(entry)
            .cloned()
            .unwrap_or_else(|| json!({"witnesses":[]}));
        let context = token::context(
            &plan,
            &id,
            &host.namespace,
            &attempt.record().identity().base_revision,
        )?;
        let client = host
            .target
            .recover_client(
                &host.store,
                &id,
                &host.descriptor,
                &serde_json::to_vec(&context)?,
            )
            .await?;
        host.finish(client).await?;
    } else {
        let deployment = host.target.start_deployment_client(
            "registerWithKey",
            &host.descriptor,
            &host.setup(&attempt_id())?,
        )?;
        host.finish(deployment).await?;
    }
    if !host.ready {
        let live = host.node.sync()?;
        let setup = host.setup(&attempt_id())?;
        let installation = host.target.start_installation_client(
            &mut host.current_state,
            &remaining_operations,
            &bootstrap_signer,
            true,
            live.block.tblock.to_secs() + 1800,
            &host.descriptor,
            &setup,
            &mut OsRng,
        )?;
        host.finish(installation).await?;
    }
    drop(bootstrap_signer);
    token::run(&mut host).await
}

fn main() {
    let result = (|| -> Result<()> {
        let mut args = std::env::args_os().skip(1);
        let path = args
            .next()
            .context("usage: confidential_token_localnet HOST_CONFIG.json")?;
        ensure!(
            args.next().is_none(),
            "usage: confidential_token_localnet HOST_CONFIG.json"
        );
        let configuration = serde_json::from_slice(&read(Path::new(&path), 32_768)?)?;
        block_on(run(configuration))
    })();
    if let Err(error) = result {
        eprintln!("token localnet example failed: {error}");
        std::process::exit(1);
    }
}
