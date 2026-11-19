//! Opt-in qualification using the publicly funded development genesis and synthetic values.
#![cfg(all(feature = "localnet", feature = "zkir-321"))]

use anyhow::{Context, Result, ensure};
use futures::{executor::block_on, future::pending};
use noctium_runtime::{
    Db, Value, artifacts,
    client::{BoundTransaction, ChainAdapter, NetworkPolicy, Submission},
    field_decimal,
    funding::{CONTRACT_SEGMENT, FeePolicy, UnsealedTransaction},
    localnet::{DevelopmentFunding, ExplicitSeal, Node, ProofCache},
    proof::{LocalProver, PreparedProof},
};
use onchain_runtime::state::{ContractState, StateValue};
use rand::{
    SeedableRng,
    rngs::{OsRng, StdRng},
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::{
    path::Path,
    time::{Duration, Instant},
};
use transient_crypto::{
    curve::{EmbeddedFr, EmbeddedGroupAffine},
    fab::AlignedValueExt,
};

fn config(receiver: EmbeddedGroupAffine, recipient: EmbeddedGroupAffine, nonce: u64) -> Vec<u8> {
    serde_json::to_vec(&json!({
        "state": {"receiverKey": Value::JubjubPoint(receiver).public_json()},
        "inputs": {
            "recipient": Value::JubjubPoint(recipient).public_json(),
            "value": "42",
            "nonce": {"kind": "jubjubScalar", "value": nonce.to_string()}
        }
    }))
    .unwrap()
}

fn decrypt(
    recipient: EmbeddedGroupAffine,
    c1: EmbeddedGroupAffine,
    c2: EmbeddedGroupAffine,
    secret: EmbeddedFr,
) -> Option<u64> {
    let generator = EmbeddedGroupAffine::generator();
    if generator * secret != recipient {
        return None;
    }
    let plaintext = c2 + c1 * (EmbeddedFr::from(0u64) - secret);
    (0..=255).find(|value| generator * EmbeddedFr::from(*value) == plaintext)
}

async fn run() -> Result<Json> {
    let settings = |name| std::env::var(name).with_context(|| format!("missing {name}"));
    let path = settings("NOCTIUM_DISCLOSURE_BUNDLE")?;
    let pin = settings("NOCTIUM_DISCLOSURE_MANIFEST_SHA256")?;
    let bundle = artifacts::verify(Path::new(&path), Some(&pin))?;
    let cache = ProofCache::new(
        settings("NOCTIUM_DISCLOSURE_PARAMETER_CACHE")?.into(),
        reqwest::Url::parse("https://srs.midnight.network/")?,
    )?;
    let policy = NetworkPolicy {
        network_id: "undeployed".into(),
        genesis: "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d".into(),
        spec_version: 2001100,
        transaction_version: 4,
        profile: noctium_runtime::profile::NAME.into(),
        max_dust: 10_000_000_000_000_000_000_000,
    };
    let node = Node::connect(
        "http://127.0.0.1:19944",
        policy.clone(),
        Duration::from_secs(30),
        64 * 1024 * 1024,
        100_000,
    )?;
    let mut seed = [0u8; 32];
    seed[31] = 1;
    node.attach_dust_seed(&seed)?;
    let snapshot = node.sync()?;
    let ttl = snapshot.block.tblock.to_secs() + 1800;

    let generator = EmbeddedGroupAffine::generator();
    let secret = EmbeddedFr::from(11u64);
    let other = EmbeddedFr::from(23u64);
    let recipient = generator * secret;
    let prepared =
        PreparedProof::from_config(&bundle, &config(recipient, recipient, 17), ttl, &mut OsRng)?;
    for rejected in [
        config(recipient, generator * other, 17),
        config(recipient, recipient, 0),
    ] {
        ensure!(
            matches!(
                PreparedProof::from_config(&bundle, &rejected, ttl, &mut OsRng),
                Err(noctium_runtime::proof::Error::InvalidPrivateInput)
            ),
            "bad disclosure was admitted"
        );
    }
    let k = prepared.k();
    let parameters = cache.parameters(k).await?;
    let call = prepared
        .prove(
            &LocalProver::new(StdRng::from_entropy()),
            &parameters,
            1_048_576,
            pending(),
        )
        .await?;
    let dust = cache.dust().await?;
    let dust_parameters = cache.parameters(dust.k()).await?;
    let (_, deploy) = prepared
        .deployment_intent()
        .context("missing deployment")?
        .prove(
            CONTRACT_SEGMENT,
            builtin_zkir::LocalProvingProvider {
                rng: StdRng::from_entropy(),
                resolver: &dust,
                params: &dust_parameters,
            },
            &snapshot.state.parameters.cost_model.runtime_cost_model,
        )
        .await?;

    let mut receipts = Vec::new();
    for intent in [&deploy, call.native()] {
        let funding = DevelopmentFunding::new(
            &node,
            &dust,
            &dust_parameters,
            FeePolicy {
                max_dust: policy.max_dust,
                margin_blocks: 3,
                max_spends: 8,
            },
            StdRng::from_entropy(),
        );
        let signing = ExplicitSeal::new(
            |_: &UnsealedTransaction, requested: &NetworkPolicy| *requested == policy,
            StdRng::from_entropy(),
        );
        let bound =
            BoundTransaction::prepare(intent, policy.clone(), &node, &funding, &signing).await?;
        ensure!(
            node.submit(&bound)
                .await
                .is_ok_and(|result| result == Submission::Broadcast),
            "development transaction was not broadcast"
        );
        let deadline = Instant::now() + Duration::from_secs(90);
        let receipt = loop {
            if let Some(receipt) = node.finalized_receipt(&bound)? {
                bound.check_receipt(&receipt)?;
                break receipt;
            }
            ensure!(
                Instant::now() < deadline,
                "development transaction did not finalize"
            );
            std::thread::sleep(Duration::from_millis(500));
        };
        receipts.push(receipt);
    }

    let call = &receipts[1];
    let state: ContractState<Db> = serialize::tagged_deserialize(&call.contract_state[..])?;
    let StateValue::Array(slots) = state.data.get_ref() else {
        anyhow::bail!("wrong state layout")
    };
    ensure!(slots.len() == 3, "unexpected public state");
    let point = |index| -> Result<EmbeddedGroupAffine> {
        let slot = slots.get(index);
        let Some(StateValue::Cell(cell)) = slot.as_deref() else {
            anyhow::bail!("missing disclosure state cell")
        };
        let mut fields = Vec::new();
        cell.value_only_field_repr(&mut fields);
        let [x, y] = fields.as_slice() else {
            anyhow::bail!("invalid disclosure point layout")
        };
        EmbeddedGroupAffine::new(*x, *y).context("invalid disclosure point")
    };
    let (receiver, c1, c2) = (point(0)?, point(1)?, point(2)?);
    ensure!(
        receiver == recipient && c1 == generator * EmbeddedFr::from(17u64),
        "unexpected key binding"
    );
    ensure!(
        decrypt(receiver, c1, c2, secret) == Some(42),
        "recipient did not recover the value"
    );
    ensure!(
        decrypt(receiver, c1, c2, other).is_none(),
        "wrong key was accepted"
    );
    let public_point =
        |p: EmbeddedGroupAffine| [field_decimal(p.x().unwrap()), field_decimal(p.y().unwrap())];
    Ok(json!({
        "profile": policy.profile, "genesis": policy.genesis, "manifestSha256": pin, "k": k,
        "parametersSha256": parameters.sha256(),
        "stateSha256": hex::encode(Sha256::digest(&call.contract_state)),
        "receiver": public_point(receiver), "ephemeral": public_point(c1), "ciphertext": public_point(c2),
        "checks": {"recipientRecovered": true, "wrongKeyRejected": true, "wrongRecipientRejected": true, "zeroNonceRejected": true},
        "receipts": receipts.iter().map(|r| json!({
            "event": r.event, "height": r.height, "blockHash": r.block_hash,
            "transactionId": r.transaction_id, "contractAddress": r.contract_address
        })).collect::<Vec<_>>()
    }))
}

#[test]
#[ignore = "requires the pinned disclosure bundle, public parameters and funded localnet"]
fn directed_disclosure_on_localnet() {
    let evidence = block_on(run()).unwrap();
    println!("{}", serde_json::to_string(&evidence).unwrap());
}
