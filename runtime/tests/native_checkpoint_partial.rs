//! Opt-in qualification against the pinned, publicly funded development genesis.
#![cfg(all(feature = "localnet", feature = "zkir-321"))]

use anyhow::{Context, Result, anyhow, ensure};
use futures::{executor::block_on, future::pending};
use ledger::structure::ContractAction;
use noctium_runtime::{
    Db, Plan, artifacts,
    client::{
        BoundTransaction, ChainAdapter, NetworkPolicy, Observation, ObservedReceipt, Submission,
        SubmissionAttempt,
    },
    create_state,
    funding::{CONTRACT_SEGMENT, FeePolicy, UnsealedTransaction},
    host,
    lifecycle::Phase,
    localnet::{
        DEVELOPMENT_GENESIS, DevelopmentFunding, ExplicitSeal, Node, ProofCache,
        journal::DirectoryJournal,
    },
    proof::{LocalProver, PreparedProof},
};
use onchain_runtime::{context::QueryContext, ops::Op, state::ContractState};
use rand::{
    RngCore, SeedableRng,
    rngs::{OsRng, StdRng},
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{
    collections::BTreeMap,
    env,
    path::{Path, PathBuf},
    thread::sleep,
    time::{Duration, Instant},
};

const NAMESPACE: &str = "checkpoint-fixture";
const KEY: &str = "test/staged";

fn staged_runtime(attempt_id: &str, address: &str, revision: &str) -> Result<host::Runtime> {
    let context = serde_json::from_value(json!({
        "protocolVersion": 1, "namespace": NAMESPACE, "baseRevision": revision,
        "attemptId": attempt_id, "providers": [], "operations": [], "commitCapability": "store",
        "capabilities": [{"id": "store", "namespace": NAMESPACE, "keyPrefix": "test/",
                          "operations": [host::STAGE, host::CAS]}]
    }))?;
    let mut runtime =
        host::Runtime::new(context, &BTreeMap::new(), address.into(), "apply".into())?;
    runtime.stage(host::Stage {
        abi_version: 1,
        operation: host::STAGE.into(),
        capability: "store".into(),
        key: KEY.into(),
        ty: "Bool".into(),
        value: json!(true),
    })?;
    runtime.execution_finished(true)?;
    Ok(runtime)
}

async fn run() -> Result<Json> {
    let setting = |name| env::var(name).with_context(|| format!("missing {name}"));
    let bundle_path = setting("NOCTIUM_CHECKPOINT_BUNDLE")?;
    let pin = setting("NOCTIUM_CHECKPOINT_MANIFEST_SHA256")?;
    let bundle = artifacts::verify(Path::new(&bundle_path), Some(&pin))?;
    let plan: Plan = serde_json::from_slice(bundle.file(artifacts::Role::Plan)?)?;
    let parameters = ProofCache::new(
        setting("NOCTIUM_CHECKPOINT_PARAMETER_CACHE")?.into(),
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
        &setting("NOCTIUM_CHECKPOINT_NODE")?,
        policy.clone(),
        Duration::from_secs(30),
        64 * 1024 * 1024,
        100_000,
    )?;
    let mut seed = [0u8; 32];
    seed[31] = 1;
    node.attach_dust_seed(&seed)?;
    let dust = parameters.dust().await?;
    let dust_srs = parameters.parameters(dust.k()).await?;
    let snapshot = node.sync()?;
    let now = snapshot.block.tblock.to_secs();
    let cutoff = now + 60;
    let configuration = serde_json::to_vec(&json!({
        "state": {"firstMark": "0", "secondMark": "0"},
        "inputs": {"cutoff": cutoff.to_string()}
    }))?;
    let prepared = PreparedProof::from_config_in_block(
        &bundle,
        &configuration,
        now + 600,
        &snapshot.block,
        &mut OsRng,
    )?;
    let call_srs = parameters.parameters(prepared.k()).await?;
    let proved = prepared
        .prove(
            &LocalProver::new(StdRng::from_entropy()),
            &call_srs,
            1_048_576,
            pending(),
        )
        .await?;
    let Some(ContractAction::Call(call)) = proved.native().actions.iter_deref().next() else {
        anyhow::bail!("expected the timed call");
    };
    let guaranteed = call
        .guaranteed_transcript
        .as_ref()
        .context("missing guaranteed prefix")?;
    let suffix = call
        .fallible_transcript
        .as_ref()
        .context("timed continuation fits in the guaranteed budget")?;
    ensure!(
        matches!(suffix.program.iter_deref().next(), Some(Op::Ckpt)),
        "continuation must start at the checkpoint"
    );

    let (_, deployment) = prepared
        .deployment_intent()
        .context("missing deployment")?
        .prove(
            CONTRACT_SEGMENT,
            builtin_zkir::LocalProvingProvider {
                rng: StdRng::from_entropy(),
                resolver: &dust,
                params: &dust_srs,
            },
            &snapshot.state.parameters.cost_model.runtime_cost_model,
        )
        .await?;
    let funding = || {
        DevelopmentFunding::new(
            &node,
            &dust,
            &dust_srs,
            FeePolicy {
                max_dust: policy.max_dust,
                margin_blocks: 3,
                max_spends: 8,
            },
            StdRng::from_entropy(),
        )
    };
    let signer = || {
        ExplicitSeal::new(
            |_: &UnsealedTransaction, requested: &NetworkPolicy| requested == &policy,
            StdRng::from_entropy(),
        )
    };
    let deploy =
        BoundTransaction::prepare(&deployment, policy.clone(), &node, &funding(), &signer())
            .await
            .context("bind deployment")?;
    ensure!(
        matches!(node.submit(&deploy).await, Ok(Submission::Broadcast)),
        "deployment did not broadcast"
    );
    let deadline = Instant::now() + Duration::from_secs(90);
    let deployed = loop {
        if let Some(receipt) = node.finalized_receipt(&deploy)? {
            deploy.check_receipt(&receipt)?;
            break receipt;
        }
        ensure!(Instant::now() < deadline, "deployment did not finalize");
        sleep(Duration::from_secs(1));
    };
    let bound = BoundTransaction::prepare(
        proved.native(),
        policy.clone(),
        &node,
        &funding(),
        &signer(),
    )
    .await
    .context("bind timed call")?;
    ensure!(
        bound.checkpoint_entrypoint() == Some(b"apply"),
        "missing signed checkpoint binding"
    );
    ensure!(
        matches!(node.observe(&bound).await, Ok(Observation::Pending)),
        "new call was not pending"
    );

    let digest = |bytes: &[u8]| hex::encode(Sha256::digest(bytes));
    let transaction_digest = digest(bound.bytes());
    let full_state_digest = digest(bound.expected_state());
    let address = bound.contract_address().to_owned();
    let mut random = [0; 32];
    OsRng.fill_bytes(&mut random);
    let attempt_id = hex::encode(random);
    let journal_dir = PathBuf::from(setting("NOCTIUM_CHECKPOINT_JOURNAL")?).join(&attempt_id);
    let store = DirectoryJournal::new(&journal_dir, Duration::from_secs(2))
        .map_err(|_| anyhow!("cannot open development journal"))?;
    let revision = store
        .revision(NAMESPACE)
        .map_err(|_| anyhow!("cannot read journal revision"))?;
    let mut runtime = staged_runtime(&attempt_id, &address, &revision)?;
    let mut attempt = SubmissionAttempt::new(bound, &attempt_id, &mut runtime)?;
    let deadline = Instant::now() + Duration::from_secs(90);
    while node.sync()?.block.tblock.to_secs() < cutoff {
        ensure!(
            Instant::now() < deadline,
            "localnet time did not advance past cutoff"
        );
        sleep(Duration::from_secs(1));
    }
    ensure!(
        matches!(
            attempt.submit_once(&mut runtime, &node, &store).await?,
            Submission::Broadcast
        ),
        "timed checkpoint call did not broadcast"
    );
    let deadline = Instant::now() + Duration::from_secs(90);
    let partial = loop {
        match attempt.observe_once(&mut runtime, &node, &store).await? {
            Some(ObservedReceipt::Partial(receipt)) => break receipt,
            Some(ObservedReceipt::Full(_)) => anyhow::bail!("expired continuation fully applied"),
            None => {}
        }
        ensure!(Instant::now() < deadline, "partial call did not finalize");
        sleep(Duration::from_secs(1));
    };
    ensure!(
        attempt.phase()? == Phase::PartiallyAccepted,
        "wrong durable phase"
    );
    let expected_prefix = create_state(
        &plan,
        &BTreeMap::from([
            ("firstMark".into(), json!("1")),
            ("secondMark".into(), json!("0")),
        ]),
    )?;
    let mut expected: ContractState<Db> =
        serialize::tagged_deserialize(&deployed.contract_state[..])?;
    let prefix = QueryContext::new(expected.data, call.address)
        .run_transcript(
            guaranteed,
            &snapshot.state.parameters.cost_model.runtime_cost_model,
        )
        .map_err(|_| anyhow!("the pinned VM did not apply the guaranteed transcript"))?;
    ensure!(
        prefix.context.state.get_ref() == expected_prefix.get_ref(),
        "wrong guaranteed prefix values"
    );
    expected.data = prefix.context.state;
    let mut prefix_bytes = Vec::new();
    serialize::tagged_serialize(&expected, &mut prefix_bytes)?;
    ensure!(
        partial.receipt.contract_state == prefix_bytes,
        "wrong finalized prefix state"
    );
    ensure!(
        digest(&prefix_bytes) != full_state_digest,
        "full and prefix states must differ"
    );
    ensure!(
        partial.entrypoint == b"apply" && partial.segments.get(&CONTRACT_SEGMENT) == Some(&false),
        "wrong signed operation or segment"
    );

    let staged_digest = digest(attempt.record().journal_bytes());
    drop(attempt);
    drop(runtime);
    drop(store);
    let store = DirectoryJournal::new(&journal_dir, Duration::from_secs(2))
        .map_err(|_| anyhow!("cannot reopen development journal"))?;
    let mut recovered = SubmissionAttempt::recover(&store, &attempt_id).await?;
    let mut runtime = staged_runtime(&attempt_id, &address, &revision)?;
    recovered.restore_runtime(&mut runtime)?;
    ensure!(
        recovered.phase()? == Phase::PartiallyAccepted
            && recovered.record().cas_receipt().is_none()
            && recovered.record().partial_receipt().is_some_and(|receipt| {
                receipt.receipt.block_hash == partial.receipt.block_hash
                    && receipt.receipt.transaction_id == partial.receipt.transaction_id
            })
            && digest(recovered.transaction().bytes()) == transaction_digest
            && digest(recovered.record().journal_bytes()) == staged_digest,
        "recovery changed the partial outcome or staged journal"
    );
    ensure!(
        recovered
            .submit_once(&mut runtime, &node, &store)
            .await
            .is_err(),
        "recovery resubmitted a finalized call"
    );
    ensure!(
        recovered
            .commit_private(&mut runtime, &store, 1)
            .await
            .is_err(),
        "recovery committed a partial call"
    );
    ensure!(
        store
            .revision(NAMESPACE)
            .map_err(|_| anyhow!("cannot read journal revision"))?
            == revision
            && store
                .private_value(NAMESPACE, KEY)
                .map_err(|_| anyhow!("cannot read development private state"))?
                .is_none(),
        "partial outcome touched the private store"
    );
    Ok(json!({
        "profile": policy.profile, "genesis": policy.genesis, "manifestSha256": pin,
        "cutoffUnix": cutoff,
        "preState": hex::encode(&deployed.contract_state), "preStateSha256": digest(&deployed.contract_state),
        "fullPredictionSha256": full_state_digest,
        "prefixPrediction": hex::encode(&prefix_bytes), "prefixPredictionSha256": digest(&prefix_bytes),
        "finalizedState": hex::encode(&partial.receipt.contract_state), "finalizedStateSha256": digest(&partial.receipt.contract_state),
        "signedTransactionSha256": transaction_digest, "transactionId": partial.receipt.transaction_id,
        "contractAddress": address, "entrypoint": "apply", "segments": partial.segments,
        "blockHash": partial.receipt.block_hash, "blockHeight": partial.receipt.height,
        "extrinsicHash": partial.receipt.extrinsic_hash, "extrinsicIndex": partial.receipt.extrinsic_index,
        "event": {"name": "TxPartialSuccess", "txHash": partial.receipt.transaction_id},
        "pendingBeforeBroadcast": true, "recoveredPartial": true, "privateStoreUnchanged": true
    }))
}

#[test]
#[ignore = "requires the compiled checkpoint bundle and funded isolated development genesis"]
fn checkpoint_prefix_finalizes_as_partial_and_recovers_with_private_writes_staged() {
    println!("{}", block_on(run()).unwrap());
}
