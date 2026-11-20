//! Explicit development-host example. No wallet seed or endpoint belongs to the SDK core.
use anyhow::{Result, anyhow, ensure};
use futures::{executor::block_on, future::pending};
use noctium_runtime::{
    artifacts,
    client::{NetworkPolicy, SubmissionAttempt},
    funding::FeePolicy,
    host,
    lifecycle::Phase,
    localnet::{DevelopmentFunding, ExplicitSeal, Node, ProofCache, journal::DirectoryJournal},
    proof::{LocalProver, PreparedProof},
};
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
use zeroize::Zeroizing;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Configuration {
    endpoint: String,
    policy: NetworkPolicy,
    bundle: PathBuf,
    manifest_sha256: String,
    private_config: PathBuf,
    parameter_cache: PathBuf,
    parameter_source: String,
    journal_directory: PathBuf,
    seed: Seed,
    approve: bool,
    wait_seconds: u64,
    resume_attempt: Option<String>,
}
#[derive(Deserialize)]
#[serde(tag = "kind", rename_all = "camelCase", deny_unknown_fields)]
enum Seed {
    PublicDevelopmentGenesis,
    File { path: PathBuf },
}
fn read(path: &Path, limit: usize) -> Result<Zeroizing<Vec<u8>>> {
    let mut bytes = Zeroizing::new(Vec::new());
    std::fs::File::open(path)?
        .take(limit as u64 + 1)
        .read_to_end(&mut bytes)?;
    ensure!(bytes.len() <= limit, "host file exceeds configured bound");
    Ok(bytes)
}
fn fresh_runtime(
    attempt: &str,
    address: &str,
    namespace: &str,
    base: &str,
) -> Result<host::Runtime> {
    let context = serde_json::from_value(
        json!({"protocolVersion":1,"namespace":namespace,"baseRevision":base,"attemptId":attempt,"capabilities":[{"id":"store","namespace":namespace,"keyPrefix":"claims/","operations":[host::STAGE,host::CAS]}],"operations":[],"providers":[],"commitCapability":"store"}),
    )?;
    let mut runtime =
        host::Runtime::new(context, &BTreeMap::new(), address.into(), "claim".into())?;
    runtime.stage(host::Stage {
        abi_version: 1,
        operation: host::STAGE.into(),
        capability: "store".into(),
        key: "claims/accepted".into(),
        ty: "Bool".into(),
        value: json!(true),
    })?;
    runtime.execution_finished(true)?;
    Ok(runtime)
}
fn recovered_runtime(attempt: &SubmissionAttempt) -> Result<host::Runtime> {
    let journal: Json = serde_json::from_slice(attempt.record().journal_bytes())?;
    let runtime = fresh_runtime(
        &attempt.record().identity().attempt_id,
        attempt.transaction().contract_address(),
        journal["namespace"]
            .as_str()
            .ok_or_else(|| anyhow!("invalid trusted journal"))?,
        &attempt.record().identity().base_revision,
    )?;
    Ok(runtime)
}
async fn finish(
    mut attempt: SubmissionAttempt,
    mut runtime: host::Runtime,
    node: &Node,
    store: &DirectoryJournal,
    wait: Duration,
) -> Result<()> {
    println!(
        "{}",
        json!({"attemptId":attempt.record().identity().attempt_id,"transactionId":attempt.transaction().transaction_id(),"contractAddress":attempt.transaction().contract_address(),"phase":format!("{:?}",attempt.phase()?)})
    );
    if matches!(
        attempt.phase()?,
        Phase::Prepared | Phase::Submitted | Phase::Uncertain
    ) {
        attempt.submit_once(&mut runtime, node, store).await?;
    }
    let deadline = Instant::now() + wait;
    let receipt = loop {
        if let Some(receipt) = attempt.observe_once(&mut runtime, node, store).await? {
            break receipt;
        }
        if Instant::now() >= deadline {
            let _ = attempt.deadline(&mut runtime, store).await;
            return Err(anyhow!(
                "submission outcome unresolved, resume the same durable attempt"
            ));
        }
        std::thread::sleep(Duration::from_millis(500));
    };
    let cas = attempt.commit_private(&mut runtime, store, 1).await?;
    println!(
        "{}",
        json!({"attemptId":attempt.record().identity().attempt_id,"transactionId":receipt.transaction_id,"contractAddress":receipt.contract_address,"event":format!("{:?}",receipt.event),"blockHash":receipt.block_hash,"height":receipt.height,"privateCommitted":cas.committed,"privateRevision":cas.revision})
    );
    Ok(())
}
async fn run(configuration: Configuration) -> Result<()> {
    ensure!(configuration.approve, "explicit host approval is required");
    ensure!(
        (1..=300).contains(&configuration.wait_seconds),
        "waitSeconds must be between 1 and 300"
    );
    // Authenticate network and negotiated metadata before opening any wallet input.
    let node = Node::connect(
        &configuration.endpoint,
        configuration.policy.clone(),
        Duration::from_secs(30),
        64 * 1024 * 1024,
        100_000,
    )?;
    let store = DirectoryJournal::new(&configuration.journal_directory, Duration::from_secs(2))
        .map_err(|_| anyhow!("trusted journal unavailable"))?;
    if let Some(id) = configuration.resume_attempt {
        let attempt = SubmissionAttempt::recover(&store, &id).await?;
        let mut runtime = recovered_runtime(&attempt)?;
        attempt.restore_runtime(&mut runtime)?;
        return finish(
            attempt,
            runtime,
            &node,
            &store,
            Duration::from_secs(configuration.wait_seconds),
        )
        .await;
    }
    let seed = match configuration.seed {
        Seed::PublicDevelopmentGenesis => {
            ensure!(
                configuration.policy.genesis
                    == "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d",
                "public fixture requires the qualified isolated development genesis"
            );
            let mut value = Zeroizing::new(vec![0; 32]);
            value[31] = 1;
            value
        }
        Seed::File { path } => {
            let value = read(&path, 32)?;
            ensure!(
                matches!(value.len(), 16 | 32),
                "seed file must contain 16 or 32 raw bytes"
            );
            value
        }
    };
    node.attach_dust_seed(&seed)?;
    drop(seed);
    let snapshot = node.sync()?;
    let cache = ProofCache::new(
        configuration.parameter_cache,
        reqwest::Url::parse(&configuration.parameter_source)?,
    )?;
    let material = cache.dust().await?;
    let dust_srs = cache.parameters(material.k()).await?;
    let bundle = artifacts::verify(&configuration.bundle, Some(&configuration.manifest_sha256))?;
    let private = read(&configuration.private_config, 1_048_576)?;
    let prepared = PreparedProof::from_config_in_block(
        &bundle,
        &private,
        snapshot.block.tblock.to_secs() + 1800,
        &snapshot.block,
        &mut OsRng,
    )?;
    let call_srs = cache.parameters(prepared.k()).await?;
    let call = prepared
        .prove(
            &LocalProver::new(StdRng::from_entropy()),
            &call_srs,
            1_048_576,
            pending(),
        )
        .await?;
    let provider = builtin_zkir::LocalProvingProvider {
        rng: StdRng::from_entropy(),
        resolver: &material,
        params: &dust_srs,
    };
    let (_, deploy) = prepared
        .deployment_intent()
        .ok_or_else(|| anyhow!("deployment material missing"))?
        .prove(
            noctium_runtime::funding::CONTRACT_SEGMENT,
            provider,
            &snapshot.state.parameters.cost_model.runtime_cost_model,
        )
        .await?;
    for intent in [&deploy, call.native()] {
        let funding = DevelopmentFunding::new(
            &node,
            &material,
            &dust_srs,
            FeePolicy {
                max_dust: configuration.policy.max_dust,
                margin_blocks: 3,
                max_spends: 8,
            },
            StdRng::from_entropy(),
        );
        let signing = ExplicitSeal::new(
            |_: &noctium_runtime::funding::UnsealedTransaction, p: &NetworkPolicy| {
                *p == configuration.policy
            },
            StdRng::from_entropy(),
        );
        let bound = noctium_runtime::client::BoundTransaction::prepare(
            intent,
            configuration.policy.clone(),
            &node,
            &funding,
            &signing,
        )
        .await?;
        let namespace = format!("native-client-{}", &bound.contract_address()[..16]);
        let base = store
            .revision(&namespace)
            .map_err(|_| anyhow!("private revision unavailable"))?;
        let mut entropy = [0; 32];
        OsRng.fill_bytes(&mut entropy);
        let id = hex::encode(entropy);
        let mut runtime = fresh_runtime(&id, bound.contract_address(), &namespace, &base)?;
        let attempt = SubmissionAttempt::new(bound, &id, &mut runtime)?;
        finish(
            attempt,
            runtime,
            &node,
            &store,
            Duration::from_secs(configuration.wait_seconds),
        )
        .await?;
    }
    Ok(())
}
fn main() {
    let result = (|| -> Result<()> {
        let mut args = std::env::args_os().skip(1);
        let path = args
            .next()
            .ok_or_else(|| anyhow!("usage: native_client HOST_CONFIG.json"))?;
        ensure!(
            args.next().is_none(),
            "usage: native_client HOST_CONFIG.json"
        );
        let bytes = read(Path::new(&path), 32_768)?;
        let configuration: Configuration =
            serde_json::from_slice(&bytes).map_err(|_| anyhow!("invalid host configuration"))?;
        block_on(run(configuration))
    })();
    if let Err(error) = result {
        eprintln!("native client failed: {error}");
        std::process::exit(1);
    }
}
