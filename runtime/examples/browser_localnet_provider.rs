//! Local provider for the browser acceptance fixture. Journals stay in the browser.
use anyhow::{Context, Result, bail, ensure};
use futures::executor::block_on;
use noctium_runtime::{
    browser_transport::{TransactionRequest, encode_snapshot},
    client::{FundingAdapter, NetworkPolicy, SigningAdapter, Snapshot, Submission},
    funding::{DustMaterial, FeePolicy, SealedTransaction, UnsealedTransaction},
    localnet::{DEVELOPMENT_GENESIS, DevelopmentFunding, ExplicitSeal, Node, ProofCache},
    proof::{ProvedNativeIntent, TrustedParameters},
};
use rand::{SeedableRng, rngs::StdRng};
use serde::Deserialize;
use serde_json::{Value, json};
use std::{
    env,
    io::{self, BufRead, Read, Write},
    path::PathBuf,
    time::Duration,
};
use zeroize::{Zeroize, Zeroizing};

const MAX_REQUEST_BYTES: usize = 12 * 1024 * 1024;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Request<'a> {
    operation: &'a str,
    private_payload: Option<&'a str>,
    transaction: Option<TransactionRequest>,
    approved: Option<bool>,
}

struct Provider {
    node: Node,
    policy: NetworkPolicy,
    dust: DustMaterial,
    parameters: TrustedParameters,
    // shortcut: one in-flight browser fixture per provider, track approvals by attempt for concurrency.
    snapshot: Option<Snapshot>,
    funded: Option<Zeroizing<Vec<u8>>>,
    sealed: Option<SealedTransaction>,
}

fn decode<T: serialize::Deserializable + serialize::Tagged>(mut bytes: &[u8]) -> Result<T> {
    let value = serialize::tagged_deserialize(&mut bytes)?;
    ensure!(bytes.is_empty(), "trailing native data");
    Ok(value)
}

fn encode<T: serialize::Serializable + serialize::Tagged>(value: &T) -> Result<Zeroizing<Vec<u8>>> {
    let mut bytes = Zeroizing::new(Vec::new());
    serialize::tagged_serialize(value, &mut *bytes)?;
    Ok(bytes)
}

fn private_payload(value: &str) -> Result<Zeroizing<Vec<u8>>> {
    ensure!(
        value
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
        "expected canonical hexadecimal"
    );
    Ok(Zeroizing::new(hex::decode(value)?))
}

impl Provider {
    async fn connect(endpoint: &str, parameters: PathBuf) -> Result<Self> {
        let url = reqwest::Url::parse(endpoint)?;
        ensure!(
            url.scheme() == "http" && matches!(url.host_str(), Some("127.0.0.1" | "[::1]")),
            "expected a loopback development node"
        );
        let policy = NetworkPolicy {
            network_id: "undeployed".into(),
            genesis: DEVELOPMENT_GENESIS.into(),
            spec_version: 2_001_100,
            transaction_version: 4,
            profile: noctium_runtime::profile::NAME.into(),
            max_dust: 10_000_000_000_000_000_000_000,
        };
        let node = Node::connect(
            endpoint,
            policy.clone(),
            Duration::from_secs(30),
            64 << 20,
            100_000,
        )?;

        let mut seed = Zeroizing::new([0u8; 32]);
        seed[31] = 1;
        node.attach_dust_seed(&*seed)?;

        let cache = ProofCache::new(
            parameters,
            reqwest::Url::parse("https://srs.midnight.network/")?,
        )?;
        let dust = cache.dust().await?;
        let parameters = cache.parameters(dust.k()).await?;
        Ok(Self {
            node,
            policy,
            dust,
            parameters,
            snapshot: None,
            funded: None,
            sealed: None,
        })
    }

    async fn reply(&mut self, request: Request<'_>) -> Result<Value> {
        match (
            request.operation,
            request.private_payload,
            request.transaction,
            request.approved,
        ) {
            ("chain.snapshot.v1", None, None, None) => {
                let snapshot = self.node.sync()?;
                let wire = encode_snapshot(&snapshot)?;
                self.snapshot = Some(snapshot);
                self.funded = None;
                Ok(json!({"kind":"snapshot","snapshot":wire}))
            }
            ("funding.native.v1", Some(payload), None, Some(true)) => {
                let bytes = private_payload(payload)?;
                let intent: ProvedNativeIntent = decode(&bytes)?;
                let funding = DevelopmentFunding::new(
                    &self.node,
                    &self.dust,
                    &self.parameters,
                    FeePolicy {
                        max_dust: self.policy.max_dust,
                        margin_blocks: 3,
                        max_spends: 8,
                    },
                    StdRng::from_entropy(),
                );
                let funded = funding
                    .fund(
                        &intent,
                        self.snapshot.as_ref().context("missing funding snapshot")?,
                        &self.policy,
                    )
                    .await
                    .map_err(|_| anyhow::anyhow!("development funding failed"))?;
                let encoded = encode(&funded)?;
                let reply = json!({"kind":"funded","transaction":hex::encode(&*encoded)});
                self.funded = Some(encoded);
                Ok(reply)
            }
            ("approval.sign.v1", Some(payload), None, Some(true)) => {
                let bytes = private_payload(payload)?;
                ensure!(
                    self.funded.as_deref() == Some(&*bytes),
                    "signing payload differs from approved development funding"
                );
                let transaction: UnsealedTransaction = decode(&bytes)?;
                let signer = ExplicitSeal::new(
                    |_: &UnsealedTransaction, policy: &NetworkPolicy| policy == &self.policy,
                    StdRng::from_entropy(),
                );
                let sealed = signer
                    .approve_and_sign(
                        &transaction,
                        self.snapshot.as_ref().context("missing signing snapshot")?,
                        &self.policy,
                    )
                    .await
                    .map_err(|_| anyhow::anyhow!("development signing failed"))?;
                let reply = json!({"kind":"signed","transaction":hex::encode(&*encode(&sealed)?)});
                self.funded = None;
                self.sealed = Some(sealed);
                Ok(reply)
            }
            ("chain.submit.v1", None, Some(tx), None) => {
                let reference = tx.reference(&self.policy)?;
                let submitted = self
                    .node
                    .submit_development_reference(
                        &reference,
                        self.sealed
                            .as_ref()
                            .context("missing development approval")?,
                    )
                    .await
                    .map_err(|_| anyhow::anyhow!("development submission failed"))?;
                let status = match submitted {
                    Submission::Broadcast => "broadcast",
                    Submission::Rejected => "rejected",
                    Submission::Uncertain => "uncertain",
                };
                Ok(json!({"kind":"submitted","status":status}))
            }
            ("chain.observe.v1", None, Some(tx), None) => {
                let reference = tx.reference(&self.policy)?;
                match self.node.observe_public_reference(&reference)? {
                    Some(receipt) => {
                        Ok(json!({"kind":"observed","status":"finalized","receipt":receipt}))
                    }
                    None => Ok(json!({"kind":"observed","status":"pending"})),
                }
            }
            _ => bail!("invalid development provider request"),
        }
    }
}

fn main() -> Result<()> {
    let mut args = env::args_os().skip(1);
    let endpoint = args.next().context("expected localnet URL")?;
    let params = args.next().context("expected proving parameter cache")?;
    ensure!(args.next().is_none(), "unexpected argument");
    let mut provider = block_on(Provider::connect(
        endpoint.to_str().context("invalid localnet URL")?,
        params.into(),
    ))?;
    let mut stdin = io::stdin().lock();
    let mut stdout = io::stdout().lock();
    loop {
        let mut bytes = Zeroizing::new(Vec::new());
        let read = stdin
            .by_ref()
            .take(MAX_REQUEST_BYTES as u64 + 1)
            .read_until(b'\n', &mut bytes)?;
        if read == 0 {
            return Ok(());
        }
        ensure!(
            read <= MAX_REQUEST_BYTES && bytes.last() == Some(&b'\n'),
            "invalid request frame"
        );
        let mut reply = match serde_json::from_slice(&bytes) {
            Ok(request) => {
                block_on(provider.reply(request)).unwrap_or_else(|_| json!({"kind":"failure"}))
            }
            Err(_) => json!({"kind":"failure"}),
        };
        let output = serde_json::to_vec(&reply).map(Zeroizing::new);
        if let Some(Value::String(transaction)) = reply.get_mut("transaction") {
            transaction.zeroize();
        }
        let output = output?;
        stdout.write_all(&output)?;
        stdout.write_all(b"\n")?;
        stdout.flush()?;
    }
}
