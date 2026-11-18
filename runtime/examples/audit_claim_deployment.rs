//! Host-side helper for check-private-claim-deployment.py. The controller owns the
//! mandatory exact-byte source audit and externally supplied trust pins.
use anyhow::{Result, anyhow, ensure};
use futures::{executor::block_on, future::pending};
use noctium_runtime::{
    artifacts::{self, Recipe, Role, Selection},
    client::{BoundTransaction, SubmissionAttempt},
    deployment_audit::{self as audit, DeploymentRecord, ObservedTransaction, Specification},
    funding::FeePolicy,
    host,
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
    cell::RefCell,
    collections::BTreeMap,
    io::Read,
    path::{Path, PathBuf},
    time::{Duration, Instant},
};
use zeroize::Zeroizing;
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Request {
    mode: String,
    specification: PathBuf,
    specification_sha256: String,
    authority: PathBuf,
    native_toolchain: PathBuf,
    srs: PathBuf,
    native_bundle: PathBuf,
    #[serde(default)]
    manifest_sha256: Option<String>,
    #[serde(default)]
    audited_artifacts: Option<PathBuf>,
    #[serde(default)]
    audited_source: Option<PathBuf>,
    #[serde(default)]
    prover_key: Option<PathBuf>,
    #[serde(default)]
    verifier_key: Option<PathBuf>,
    #[serde(default)]
    ledger_parameters: Option<PathBuf>,
    #[serde(default)]
    abi: Option<PathBuf>,
    #[serde(default)]
    endpoint: Option<String>,
    #[serde(default)]
    parameter_cache: Option<PathBuf>,
    #[serde(default)]
    private_config: Option<PathBuf>,
    #[serde(default)]
    journal_directory: Option<PathBuf>,
    #[serde(default)]
    public_development_genesis: bool,
    #[serde(default)]
    approve: bool,
    #[serde(default)]
    record: Option<PathBuf>,
    #[serde(default)]
    record_sha256: Option<String>,
    #[serde(default)]
    expected_address: Option<String>,
}
fn read(path: &Path, limit: usize) -> Result<Zeroizing<Vec<u8>>> {
    let mut bytes = Zeroizing::new(Vec::new());
    std::fs::File::open(path)?
        .take(limit as u64 + 1)
        .read_to_end(&mut bytes)?;
    ensure!(bytes.len() <= limit, "input_limit");
    Ok(bytes)
}
fn path<'a>(value: &'a Option<PathBuf>) -> Result<&'a Path> {
    Ok(value
        .as_deref()
        .ok_or_else(|| anyhow!("missing_host_path"))?)
}
fn make_runtime(id: &str, address: &str, base: &str) -> Result<host::Runtime> {
    let ns = format!("deployment-audit-{}", &address[..16]);
    let context = serde_json::from_value(
        json!({"protocolVersion":1,"namespace":ns,"baseRevision":base,"attemptId":id,"capabilities":[{"id":"store","namespace":ns,"keyPrefix":"claims/","operations":[host::STAGE,host::CAS]}],"operations":[],"providers":[],"commitCapability":"store"}),
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
struct QuotedFunding<'a, 'b> {
    inner: DevelopmentFunding<'a>,
    material: &'a audit::QualifiedMaterial<'b>,
    spec: &'a Specification,
    node: &'a Node,
    quote: RefCell<Option<audit::FundingQuote>>,
}
impl noctium_runtime::client::FundingAdapter for QuotedFunding<'_, '_> {
    async fn fund(
        &self,
        contract: &noctium_runtime::proof::ProvedNativeIntent,
        snapshot: &noctium_runtime::client::Snapshot,
        policy: &noctium_runtime::client::NetworkPolicy,
    ) -> std::result::Result<
        noctium_runtime::funding::UnsealedTransaction,
        noctium_runtime::client::HostFailure,
    > {
        let quote = self
            .material
            .check_live(self.spec, snapshot, self.node.runtime_fingerprint())
            .map_err(|_| noctium_runtime::client::HostFailure)?;
        let native = noctium_runtime::client::FundingAdapter::fund(
            &self.inner,
            contract,
            snapshot,
            policy,
        )
        .await?;
        *self.quote.borrow_mut() = Some(quote);
        Ok(native)
    }
}

async fn submit(
    bound: BoundTransaction,
    node: &Node,
    store: &DirectoryJournal,
    funding_quote: audit::FundingQuote,
) -> Result<ObservedTransaction> {
    let bytes = bound.bytes().to_vec();
    let after_height = bound.after_height();
    let address = bound.contract_address().to_owned();
    let base = store
        .revision(&format!("deployment-audit-{}", &address[..16]))
        .map_err(|_| anyhow!("journal_unavailable"))?;
    let mut entropy = [0; 32];
    OsRng.fill_bytes(&mut entropy);
    let id = hex::encode(entropy);
    let mut runtime = make_runtime(&id, &address, &base)?;
    let mut attempt = SubmissionAttempt::new(bound, &id, &mut runtime)?;
    attempt.submit_once(&mut runtime, node, store).await?;
    let deadline = Instant::now() + Duration::from_secs(90);
    let receipt = loop {
        if let Some(value) = attempt.observe_once(&mut runtime, node, store).await? {
            break value;
        }
        if Instant::now() >= deadline {
            let _ = attempt.deadline(&mut runtime, store).await;
            return Err(anyhow!("durable_attempt_outcome_uncertain"));
        }
        std::thread::sleep(Duration::from_millis(500));
    };
    ensure!(
        attempt
            .commit_private(&mut runtime, store, 1)
            .await?
            .committed,
        "private_revision_conflict"
    );
    Ok(ObservedTransaction {
        native_transaction_hex: hex::encode(bytes),
        after_height,
        funding_quote,
        receipt,
    })
}
async fn run(request: Request) -> Result<Json> {
    let spec_bytes = read(&request.specification, 65536)?;
    ensure!(
        audit::hash(&spec_bytes) == request.specification_sha256,
        "external_specification_mismatch"
    );
    let spec: Specification = serde_json::from_slice(&spec_bytes)?;
    spec.validate()?;
    if request.mode == "measure-parameters" {
        ensure!(
            request.private_config.is_none()
                && request.journal_directory.is_none()
                && !request.public_development_genesis,
            "public_measurement_rejects_private_inputs"
        );
        let node = Node::connect(
            request
                .endpoint
                .as_deref()
                .ok_or_else(|| anyhow!("missing_node_endpoint"))?,
            spec.policy.clone(),
            Duration::from_secs(30),
            64 * 1024 * 1024,
            100_000,
        )?;
        ensure!(
            node.runtime_fingerprint()
                == (spec.runtime_code_hash.clone(), spec.metadata_sha256.clone()),
            "runtime_identity_mismatch"
        );
        let snapshot = node.sync()?;
        let bytes = audit::encode(&*snapshot.state.parameters)?;
        std::fs::write(path(&request.ledger_parameters)?, &bytes)?;
        return Ok(
            json!({"status":"measurement-only-not-an-authority","ledgerParametersSha256":audit::hash(&bytes),"finalizedHash":snapshot.finalized_hash,"height":snapshot.height}),
        );
    }
    let authority = read(&request.authority, 2 * 1024 * 1024)?;
    let toolchain = read(&request.native_toolchain, 65536)?;
    let srs = read(&request.srs, 128 * 1024 * 1024)?;
    let manifest = if request.mode == "prepare" {
        ensure!(
            request.private_config.is_none()
                && request.journal_directory.is_none()
                && !request.public_development_genesis,
            "public_build_rejects_private_inputs"
        );
        let dir = path(&request.audited_artifacts)?;
        let source = path(&request.audited_source)?;
        let selections = vec![
            Selection {
                role: Role::Source,
                name: "examples/PrivateClaim.lean".into(),
                input: source.join("examples/PrivateClaim.lean"),
            },
            Selection {
                role: Role::Circuit,
                name: "PrivateClaim.claim.zkir".into(),
                input: dir.join("PrivateClaim.claim.zkir"),
            },
            Selection {
                role: Role::Plan,
                name: "PrivateClaim.claim.impact.json".into(),
                input: dir.join("PrivateClaim.claim.impact.json"),
            },
            Selection {
                role: Role::Metadata,
                name: "noctium.json".into(),
                input: dir.join("noctium.json"),
            },
            Selection {
                role: Role::Profile,
                name: "target.json".into(),
                input: dir.join("target-profile.json"),
            },
            Selection {
                role: Role::Abi,
                name: "abi.schema.json".into(),
                input: path(&request.abi)?.into(),
            },
            Selection {
                role: Role::LedgerParameters,
                name: "ledger.params".into(),
                input: path(&request.ledger_parameters)?.into(),
            },
            Selection {
                role: Role::ProverKey,
                name: "entrypoint.prover".into(),
                input: path(&request.prover_key)?.into(),
            },
            Selection {
                role: Role::VerifierKey,
                name: "entrypoint.verifier".into(),
                input: path(&request.verifier_key)?.into(),
            },
            Selection {
                role: Role::Toolchain,
                name: "native-zkir.json".into(),
                input: request.native_toolchain.clone(),
            },
        ];
        let manifest = artifacts::assemble(
            Recipe {
                schema_version: 1,
                compiler_revision: spec.source_commit.clone(),
                files: selections,
            },
            &request.native_bundle,
        )?;
        artifacts::digest(&artifacts::manifest_bytes(&manifest)?)
    } else {
        request
            .manifest_sha256
            .clone()
            .ok_or_else(|| anyhow!("missing_manifest_pin"))?
    };
    let bundle = artifacts::verify(&request.native_bundle, Some(&manifest))?;
    let material = audit::qualify(&spec, &authority, &bundle, &srs, &toolchain).await?;
    if request.mode == "prepare" {
        return Ok(
            json!({"status":"public-native-material-qualified","manifestSha256":manifest,"materialIdentity":material.identity,"privateInvocationInputsConsumed":false}),
        );
    }
    let endpoint = request
        .endpoint
        .as_deref()
        .ok_or_else(|| anyhow!("missing_node_endpoint"))?;
    let public_node = Node::connect(
        endpoint,
        spec.policy.clone(),
        Duration::from_secs(30),
        64 * 1024 * 1024,
        100_000,
    )?;
    let snapshot = public_node.sync()?;
    material.check_parameter_reference(&spec, &public_node)?;
    material.check_live(&spec, &snapshot, public_node.runtime_fingerprint())?;
    if request.mode == "verify" {
        ensure!(
            request.private_config.is_none()
                && request.journal_directory.is_none()
                && !request.public_development_genesis,
            "public_verifier_rejects_private_inputs"
        );
        let bytes = read(path(&request.record)?, 16 * 1024 * 1024)?;
        ensure!(
            Some(audit::hash(&bytes)) == request.record_sha256,
            "external_deployment_record_mismatch"
        );
        let record: DeploymentRecord = serde_json::from_slice(&bytes)?;
        return audit::observe_record(
            &spec,
            &spec_bytes,
            &material,
            &record,
            request
                .expected_address
                .as_deref()
                .ok_or_else(|| anyhow!("missing_expected_address"))?,
            &public_node,
        );
    }
    ensure!(
        request.mode == "execute" && request.approve && request.public_development_genesis,
        "explicit_development_execution_approval_required"
    );
    ensure!(
        spec.policy.genesis == "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d",
        "public_fixture_genesis_mismatch"
    );
    let node = Node::connect(
        endpoint,
        spec.policy.clone(),
        Duration::from_secs(30),
        64 * 1024 * 1024,
        100_000,
    )?;
    let mut seed = Zeroizing::new([0; 32]);
    seed[31] = 1;
    node.attach_dust_seed(&*seed)?;
    drop(seed);
    let live = node.sync()?;
    material.check_live(&spec, &live, node.runtime_fingerprint())?;
    let private = read(path(&request.private_config)?, 1_048_576)?;
    let prepared = PreparedProof::from_config(
        &bundle,
        &private,
        live.block.tblock.to_secs() + 1800,
        &mut OsRng,
    )?;
    let deploy = prepared
        .deployment_intent()
        .ok_or_else(|| anyhow!("missing_deployment"))?;
    let Some(ledger::structure::ContractAction::Deploy(deployment)) =
        deploy.actions.iter_deref().next()
    else {
        return Err(anyhow!("missing_deployment"));
    };
    material.check_initial(&audit::encode(&deployment.initial_state)?)?;
    let call = prepared
        .prove(
            &LocalProver::new(StdRng::from_entropy()),
            &material.parameters,
            1_048_576,
            pending(),
        )
        .await?;
    let cache = ProofCache::new(
        path(&request.parameter_cache)?.into(),
        reqwest::Url::parse("https://srs.midnight.network/")?,
    )?;
    let dust = cache.dust().await?;
    let dust_params = cache.parameters(dust.k()).await?;
    let provider = builtin_zkir::LocalProvingProvider {
        rng: StdRng::from_entropy(),
        resolver: &dust,
        params: &dust_params,
    };
    let (_, deploy) = deploy
        .prove(
            noctium_runtime::funding::CONTRACT_SEGMENT,
            provider,
            &live.state.parameters.cost_model.runtime_cost_model,
        )
        .await?;
    let store = DirectoryJournal::new(path(&request.journal_directory)?, Duration::from_secs(2))
        .map_err(|_| anyhow!("journal_unavailable"))?;
    let mut observations = Vec::new();
    for intent in [&deploy, call.native()] {
        let funding = DevelopmentFunding::new(
            &node,
            &dust,
            &dust_params,
            FeePolicy {
                max_dust: spec.policy.max_dust,
                margin_blocks: 3,
                max_spends: 8,
            },
            StdRng::from_entropy(),
        );
        let funding = QuotedFunding {
            inner: funding,
            material: &material,
            spec: &spec,
            node: &node,
            quote: RefCell::new(None),
        };
        let signing = ExplicitSeal::new(
            |_: &noctium_runtime::funding::UnsealedTransaction,
             p: &noctium_runtime::client::NetworkPolicy| *p == spec.policy,
            StdRng::from_entropy(),
        );
        let bound =
            BoundTransaction::prepare(intent, spec.policy.clone(), &node, &funding, &signing)
                .await?;
        let quote = funding
            .quote
            .borrow_mut()
            .take()
            .ok_or_else(|| anyhow!("missing_funding_quote"))?;
        observations.push(submit(bound, &node, &store, quote).await?);
    }
    let call = observations.pop().unwrap();
    let deployment = observations.pop().unwrap();
    let address = deployment.receipt.contract_address.clone();
    let record = DeploymentRecord {
        schema_version: 1,
        guarantee_version: audit::GUARANTEE.into(),
        specification_sha256: request.specification_sha256,
        material_identity: material.identity.clone(),
        address: address.clone(),
        deployment,
        call,
    };
    let outcome = audit::observe_record(
        &spec,
        &spec_bytes,
        &material,
        &record,
        &address,
        &public_node,
    )?;
    std::fs::write(path(&request.record)?, serde_json::to_vec_pretty(&record)?)?;
    Ok(
        json!({"status":"native-deployment-and-claim-qualified","address":address,"deploymentRecordSha256":audit::hash(&read(path(&request.record)?,16*1024*1024)?),"audit":outcome}),
    )
}
fn main() {
    let result = (|| -> Result<Json> {
        let args: Vec<_> = std::env::args_os().skip(1).collect();
        ensure!(
            args.len() == 1,
            "usage: audit_claim_deployment REQUEST.json"
        );
        let bytes = read(Path::new(&args[0]), 65536)?;
        let request: Request =
            serde_json::from_slice(&bytes).map_err(|_| anyhow!("invalid_host_request"))?;
        block_on(run(request))
    })();
    match result {
        Ok(value) => println!("{value}"),
        Err(error) => {
            eprintln!("deployment_audit_rejected: {error}");
            std::process::exit(1);
        }
    }
}
