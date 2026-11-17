//! Owned native client tasks. Transport, wallet, approval and durable stores are explicit services.
use crate::{
    assembly::NativeIntent,
    client::{
        self, BoundTransaction, CasReceipt, ChainAdapter, FinalizedReceipt, FundingAdapter,
        HostFailure, JournalStore, NetworkPolicy, Observation, RecoveryRecord, SigningAdapter,
        Snapshot, StoreAcknowledgement, StoredRecord, Submission, SubmissionAttempt,
    },
    funding::{SealedTransaction, UnsealedTransaction},
    host,
    lifecycle::Phase,
    proof::ProvedNativeIntent,
};
use futures::{Future, channel::oneshot, task::noop_waker};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    pin::Pin,
    sync::{
        Arc, Mutex,
        atomic::{AtomicU64, Ordering},
    },
    task::{Context, Poll},
};
use zeroize::Zeroizing;
const MAX_REQUESTS: usize = 1024;
static NEXT_REQUEST: AtomicU64 = AtomicU64::new(1);
#[derive(Clone, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Capabilities {
    pub chain: String,
    pub funding: String,
    pub signing: String,
    pub journal: String,
}
impl Capabilities {
    pub fn validate(&self) -> bool {
        [&self.chain, &self.funding, &self.signing, &self.journal]
            .iter()
            .all(|s| {
                !s.is_empty()
                    && s.len() <= 128
                    && s.bytes()
                        .all(|b| b.is_ascii_alphanumeric() || b"._-".contains(&b))
            })
    }
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Descriptor {
    pub abi_version: u32,
    #[serde(deserialize_with = "policy")]
    pub policy: NetworkPolicy,
    pub capabilities: Capabilities,
}
pub(crate) fn policy<'de, D: serde::Deserializer<'de>>(d: D) -> Result<NetworkPolicy, D::Error> {
    #[derive(Deserialize)]
    #[serde(rename_all = "camelCase", deny_unknown_fields)]
    struct Wire {
        network_id: String,
        genesis: String,
        spec_version: u32,
        transaction_version: u32,
        profile: String,
        max_dust: String,
    }
    let w = Wire::deserialize(d)?;
    let amount = w
        .max_dust
        .parse::<u128>()
        .ok()
        .filter(|v| v.to_string() == w.max_dust && *v > 0)
        .ok_or_else(|| serde::de::Error::custom("invalid_native_budget"))?;
    Ok(NetworkPolicy {
        network_id: w.network_id,
        genesis: w.genesis,
        spec_version: w.spec_version,
        transaction_version: w.transaction_version,
        profile: w.profile,
        max_dust: amount,
    })
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub(crate) struct Setup {
    pub host_context: host::Context,
    pub stages: Vec<host::Stage>,
}
pub(crate) enum Contract {
    Proved(ProvedNativeIntent),
    Deployment {
        intent: ProvedNativeIntent,
        entrypoint: String,
    },
}
fn snapshot_copy(s: &Snapshot) -> Snapshot {
    Snapshot {
        chain: s.chain.clone(),
        finalized_hash: s.finalized_hash.clone(),
        height: s.height,
        state: s.state.clone(),
        block: s.block.clone(),
    }
}
fn record_copy(r: &RecoveryRecord) -> Result<RecoveryRecord, HostFailure> {
    serde_json::from_slice(&r.private_bytes().map_err(|_| HostFailure)?).map_err(|_| HostFailure)
}
pub(crate) enum RequestData {
    Snapshot,
    Fund {
        contract: ProvedNativeIntent,
        snapshot: Snapshot,
    },
    Sign {
        transaction: UnsealedTransaction,
        snapshot: Snapshot,
    },
    Submit(BoundTransaction),
    Observe(BoundTransaction),
    Load(String),
    Persist {
        record: RecoveryRecord,
        expected_revision: Option<u64>,
    },
    Cas(RecoveryRecord),
}
pub(crate) enum ServiceReply {
    Snapshot(Snapshot),
    Funded(UnsealedTransaction),
    Signed(SealedTransaction),
    Submitted(Submission),
    Observed(Observation),
    Loaded(StoredRecord),
    Persisted(StoreAcknowledgement),
    Cas(CasReceipt),
    Failure,
}
pub(crate) struct Request {
    pub id: u64,
    pub operation: &'static str,
    pub capability: String,
    pub schema: &'static str,
    pub policy: NetworkPolicy,
    pub data: RequestData,
}
impl Request {
    pub fn metadata(&self) -> Json {
        json!({"abiVersion":1,"status":"need_host","requestId":self.id.to_string(),"operation":self.operation,"capability":self.capability,"schema":self.schema,"profile":crate::profile::NAME,"hasPrivateArguments":matches!(self.data,RequestData::Fund{..}|RequestData::Sign{..}|RequestData::Load(_)|RequestData::Persist{..}|RequestData::Cas(_))})
    }
    pub fn accepts(&self, reply: &ServiceReply) -> bool {
        matches!(
            (&self.data, reply),
            (_, ServiceReply::Failure)
                | (RequestData::Snapshot, ServiceReply::Snapshot(_))
                | (RequestData::Fund { .. }, ServiceReply::Funded(_))
                | (RequestData::Sign { .. }, ServiceReply::Signed(_))
                | (RequestData::Submit(_), ServiceReply::Submitted(_))
                | (RequestData::Observe(_), ServiceReply::Observed(_))
                | (RequestData::Load(_), ServiceReply::Loaded(_))
                | (RequestData::Persist { .. }, ServiceReply::Persisted(_))
                | (RequestData::Cas(_), ServiceReply::Cas(_))
        )
    }
    pub fn private_bytes(&self) -> Result<Zeroizing<Vec<u8>>, client::Error> {
        match &self.data {
            RequestData::Persist { record, .. } | RequestData::Cas(record) => {
                record.private_bytes()
            }
            RequestData::Fund { contract, .. } => encode(contract).map(Zeroizing::new),
            RequestData::Sign { transaction, .. } => encode(transaction).map(Zeroizing::new),
            RequestData::Load(attempt) => Ok(Zeroizing::new(attempt.as_bytes().to_vec())),
            _ => Err(client::Error::State),
        }
    }
}
fn encode<T: serialize::Serializable + serialize::Tagged>(v: &T) -> Result<Vec<u8>, client::Error> {
    let mut b = Vec::new();
    serialize::tagged_serialize(v, &mut b).map_err(|_| client::Error::InvalidTransaction)?;
    Ok(b)
}
struct Pending {
    request: Arc<Request>,
    sender: oneshot::Sender<ServiceReply>,
}
struct Mailbox {
    pending: Option<Pending>,
    count: usize,
}
#[derive(Clone)]
struct Adapter {
    mailbox: Arc<Mutex<Mailbox>>,
    capabilities: Capabilities,
    policy: NetworkPolicy,
}
impl Adapter {
    async fn exchange(&self, data: RequestData) -> Result<ServiceReply, HostFailure> {
        let (operation, capability, schema) = match &data {
            RequestData::Snapshot => (
                "chain.snapshot.v1",
                &self.capabilities.chain,
                "native.snapshot.v1",
            ),
            RequestData::Fund { .. } => (
                "funding.native.v1",
                &self.capabilities.funding,
                "native.unsealed-transaction.v1",
            ),
            RequestData::Sign { .. } => (
                "approval.sign.v1",
                &self.capabilities.signing,
                "native.sealed-transaction.v1",
            ),
            RequestData::Submit(_) => (
                "chain.submit.v1",
                &self.capabilities.chain,
                "native.submission.v1",
            ),
            RequestData::Observe(_) => (
                "chain.observe.v1",
                &self.capabilities.chain,
                "native.finalized-receipt.v1",
            ),
            RequestData::Load(_) => (
                "journal.load.v1",
                &self.capabilities.journal,
                "native.trusted-record.v1",
            ),
            RequestData::Persist { .. } => (
                "journal.persist.v1",
                &self.capabilities.journal,
                "native.durable-ack.v1",
            ),
            RequestData::Cas(_) => (
                "private_state.compare_exchange.v1",
                &self.capabilities.journal,
                "native.cas-receipt.v1",
            ),
        };
        let (sender, receiver) = oneshot::channel();
        {
            let mut m = self.mailbox.lock().map_err(|_| HostFailure)?;
            if m.pending.is_some() || m.count >= MAX_REQUESTS {
                return Err(HostFailure);
            }
            let id = NEXT_REQUEST
                .try_update(Ordering::Relaxed, Ordering::Relaxed, |v| v.checked_add(1))
                .map_err(|_| HostFailure)?;
            m.count += 1;
            m.pending = Some(Pending {
                request: Arc::new(Request {
                    id,
                    operation,
                    capability: capability.clone(),
                    schema,
                    policy: self.policy.clone(),
                    data,
                }),
                sender,
            });
        }
        receiver.await.map_err(|_| HostFailure)
    }
}
impl ChainAdapter for Adapter {
    async fn snapshot(&self) -> Result<Snapshot, HostFailure> {
        match self.exchange(RequestData::Snapshot).await? {
            ServiceReply::Snapshot(s) => Ok(s),
            _ => Err(HostFailure),
        }
    }
    async fn submit(&self, t: &BoundTransaction) -> Result<Submission, HostFailure> {
        match self.exchange(RequestData::Submit(t.clone())).await? {
            ServiceReply::Submitted(s) => Ok(s),
            _ => Err(HostFailure),
        }
    }
    async fn observe(&self, t: &BoundTransaction) -> Result<Observation, HostFailure> {
        match self.exchange(RequestData::Observe(t.clone())).await? {
            ServiceReply::Observed(s) => Ok(s),
            _ => Err(HostFailure),
        }
    }
}
impl FundingAdapter for Adapter {
    async fn fund(
        &self,
        c: &ProvedNativeIntent,
        s: &Snapshot,
        p: &NetworkPolicy,
    ) -> Result<UnsealedTransaction, HostFailure> {
        if *p != self.policy {
            return Err(HostFailure);
        }
        match self
            .exchange(RequestData::Fund {
                contract: c.clone(),
                snapshot: snapshot_copy(s),
            })
            .await?
        {
            ServiceReply::Funded(t) => Ok(t),
            _ => Err(HostFailure),
        }
    }
}
impl SigningAdapter for Adapter {
    async fn approve_and_sign(
        &self,
        t: &UnsealedTransaction,
        s: &Snapshot,
        p: &NetworkPolicy,
    ) -> Result<SealedTransaction, HostFailure> {
        if *p != self.policy {
            return Err(HostFailure);
        }
        match self
            .exchange(RequestData::Sign {
                transaction: t.clone(),
                snapshot: snapshot_copy(s),
            })
            .await?
        {
            ServiceReply::Signed(t) => Ok(t),
            _ => Err(HostFailure),
        }
    }
}
impl JournalStore for Adapter {
    async fn load(&self, id: &str) -> Result<StoredRecord, HostFailure> {
        match self.exchange(RequestData::Load(id.into())).await? {
            ServiceReply::Loaded(r) => Ok(r),
            _ => Err(HostFailure),
        }
    }
    async fn persist(
        &self,
        r: &RecoveryRecord,
        expected_revision: Option<u64>,
    ) -> Result<StoreAcknowledgement, HostFailure> {
        match self
            .exchange(RequestData::Persist {
                record: record_copy(r)?,
                expected_revision,
            })
            .await?
        {
            ServiceReply::Persisted(a) => Ok(a),
            _ => Err(HostFailure),
        }
    }
    async fn compare_exchange(&self, r: &RecoveryRecord) -> Result<CasReceipt, HostFailure> {
        match self.exchange(RequestData::Cas(record_copy(r)?)).await? {
            ServiceReply::Cas(c) => Ok(c),
            _ => Err(HostFailure),
        }
    }
}
fn address(c: &Contract) -> Result<(String, String), client::Error> {
    use ledger::structure::ContractAction;
    let (a, entry) = match c {
        Contract::Proved(i) => match i.actions.iter_deref().next() {
            Some(ContractAction::Call(c)) => (
                c.address,
                String::from_utf8(c.entry_point.0.clone()).map_err(|_| client::Error::Identity)?,
            ),
            Some(ContractAction::Deploy(d)) => (d.address(), "claim".into()),
            _ => return Err(client::Error::Identity),
        },
        Contract::Deployment { intent, entrypoint } => match intent.actions.iter_deref().next() {
            Some(ContractAction::Deploy(d)) => (d.address(), entrypoint.clone()),
            _ => return Err(client::Error::Identity),
        },
    };
    Ok((hex::encode(a.0.0), entry))
}
struct State {
    policy: NetworkPolicy,
    contract: Option<Contract>,
    runtime: Option<host::Runtime>,
    attempt: Option<SubmissionAttempt>,
    context: Zeroizing<Vec<u8>>,
    receipt: Option<FinalizedReceipt>,
    durable: bool,
    cancelled: bool,
}
fn restored_runtime(
    context: &[u8],
    attempt: &SubmissionAttempt,
) -> Result<host::Runtime, client::Error> {
    let ctx: host::Context =
        serde_json::from_slice(context).map_err(|_| client::Error::Identity)?;
    let journal: Json = serde_json::from_slice(attempt.record().journal_bytes())
        .map_err(|_| client::Error::Identity)?;
    if journal["attemptId"] != ctx.attempt_id
        || journal["baseRevision"] != ctx.base_revision
        || journal["namespace"] != ctx.namespace
    {
        return Err(client::Error::Identity);
    }
    let target = journal["contractAddress"]
        .as_str()
        .ok_or(client::Error::Identity)?
        .into();
    let entry = journal["entrypoint"]
        .as_str()
        .ok_or(client::Error::Identity)?
        .into();
    let capabilities: Vec<_> = ctx
        .capabilities
        .iter()
        .map(|c| {
            (
                c.id.clone(),
                c.key_prefix.clone(),
                c.operations.contains(&host::STAGE.into()),
            )
        })
        .collect();
    let mut runtime = host::Runtime::new(ctx, &BTreeMap::new(), target, entry)
        .map_err(|_| client::Error::Identity)?;
    for (key, write) in journal["writes"]
        .as_object()
        .ok_or(client::Error::Identity)?
    {
        let cap = capabilities
            .iter()
            .find(|(_, prefix, stage)| *stage && key.starts_with(prefix))
            .ok_or(client::Error::Identity)?;
        runtime
            .stage(host::Stage {
                abi_version: 1,
                operation: host::STAGE.into(),
                capability: cap.0.clone(),
                key: key.clone(),
                ty: write["type"]
                    .as_str()
                    .ok_or(client::Error::Identity)?
                    .into(),
                value: write["value"].clone(),
            })
            .map_err(|_| client::Error::Identity)?;
    }
    runtime
        .execution_finished(true)
        .map_err(|_| client::Error::State)?;
    attempt.restore_runtime(&mut runtime)?;
    Ok(runtime)
}
#[derive(Clone, Copy, Eq, PartialEq)]
pub(crate) enum Command {
    Prepare,
    Submit,
    Observe,
    Commit,
    Cancel,
    Deadline,
    Reload,
}
impl Command {
    pub fn parse(s: &str) -> Option<Self> {
        Some(match s {
            "prepare" => Self::Prepare,
            "submit" => Self::Submit,
            "observe" => Self::Observe,
            "commit" => Self::Commit,
            "cancel" => Self::Cancel,
            "deadline" => Self::Deadline,
            "reload" => Self::Reload,
            _ => return None,
        })
    }
}
// A deployment contains no call/dust preimage. Ask the native prover to preserve that fact.
#[derive(Clone)]
struct NoProof;
impl transient_crypto::proofs::Resolver for NoProof {
    async fn resolve_key(
        &self,
        _: transient_crypto::proofs::KeyLocation,
    ) -> std::io::Result<Option<transient_crypto::proofs::ProvingKeyMaterial>> {
        Ok(None)
    }
}
impl transient_crypto::proofs::ProvingProvider for NoProof {
    async fn check(
        &self,
        _: &transient_crypto::proofs::ProofPreimage,
    ) -> anyhow::Result<Vec<Option<usize>>> {
        Err(anyhow::anyhow!("deployment_has_no_proof"))
    }
    async fn prove(
        self,
        _: &transient_crypto::proofs::ProofPreimage,
        _: Option<transient_crypto::curve::Fr>,
    ) -> anyhow::Result<transient_crypto::proofs::Proof> {
        Err(anyhow::anyhow!("deployment_has_no_proof"))
    }
    fn split(&mut self) -> Self {
        self.clone()
    }
    fn resolver(&self) -> &impl transient_crypto::proofs::Resolver {
        self
    }
}
pub(crate) fn prove_deployment(
    intent: &NativeIntent,
    parameters: &ledger::structure::LedgerParameters,
) -> Result<ProvedNativeIntent, client::Error> {
    use ledger::structure::ContractAction;
    if intent.actions.len() != 1
        || !matches!(
            intent.actions.iter_deref().next(),
            Some(ContractAction::Deploy(_))
        )
        || intent.dust_actions.is_some()
        || intent.guaranteed_unshielded_offer.is_some()
        || intent.fallible_unshielded_offer.is_some()
    {
        return Err(client::Error::InvalidTransaction);
    }
    futures::executor::block_on(intent.prove(
        crate::funding::CONTRACT_SEGMENT,
        NoProof,
        &parameters.cost_model.runtime_cost_model,
    ))
    .map(|(_, i)| i)
    .map_err(|_| client::Error::InvalidTransaction)
}
async fn step(
    mut state: State,
    command: Command,
    adapter: Adapter,
) -> (State, Result<Json, client::Error>) {
    let result = async {
        match command {
            Command::Prepare => {
                let contract = match &state.contract {
                    Some(Contract::Proved(i)) | Some(Contract::Deployment { intent: i, .. }) => i,
                    _ => return Err(client::Error::State),
                };
                let bound = BoundTransaction::prepare(
                    contract,
                    state.policy.clone(),
                    &adapter,
                    &adapter,
                    &adapter,
                )
                .await?;
                let ctx: host::Context =
                    serde_json::from_slice(&state.context).map_err(|_| client::Error::Identity)?;
                state.attempt = Some(SubmissionAttempt::new(
                    bound,
                    &ctx.attempt_id,
                    state.runtime.as_mut().ok_or(client::Error::State)?,
                )?);
            }
            Command::Reload => {
                let ctx: host::Context =
                    serde_json::from_slice(&state.context).map_err(|_| client::Error::Identity)?;
                let attempt = SubmissionAttempt::recover(&adapter, &ctx.attempt_id).await?;
                if attempt.transaction().policy() != &state.policy {
                    return Err(client::Error::Network);
                }
                state.runtime = Some(restored_runtime(&state.context, &attempt)?);
                state.receipt = None;
                state.attempt = Some(attempt);
                state.contract = None;
                state.durable = true;
            }
            command => {
                let attempt = state.attempt.as_mut().ok_or(client::Error::State)?;
                let runtime = state.runtime.as_mut().ok_or(client::Error::State)?;
                match command {
                    Command::Submit => {
                        attempt.submit_once(runtime, &adapter, &adapter).await?;
                        state.durable = true;
                    }
                    Command::Observe => {
                        let terminal =
                            matches!(attempt.phase()?, Phase::Committed | Phase::Conflicted);
                        if let Some(receipt) =
                            attempt.observe_once(runtime, &adapter, &adapter).await?
                        {
                            state.receipt = Some(receipt);
                            if !terminal {
                                state.durable = true
                            }
                        }
                    }
                    Command::Commit => {
                        attempt.commit_private(runtime, &adapter, 1).await?;
                        state.durable = true;
                    }
                    Command::Cancel => {
                        attempt.cancel(runtime, &adapter).await?;
                        state.durable = true;
                        state.cancelled = true;
                    }
                    Command::Deadline => {
                        let phase = attempt.phase()?;
                        if phase == Phase::Cancelled {
                            attempt.cancel(runtime, &adapter).await?;
                            state.durable = true;
                            return Err(client::Error::Deadline);
                        }
                        let result = attempt.deadline(runtime, &adapter).await;
                        if result == Err(client::Error::Deadline)
                            && matches!(
                                phase,
                                Phase::Prepared | Phase::Submitted | Phase::Uncertain
                            )
                        {
                            state.durable = true;
                        }
                        result?;
                    }
                    _ => return Err(client::Error::State),
                }
            }
        }
        Ok(json!({"status":"step_done"}))
    }
    .await;
    if result.is_err() && !(command == Command::Deadline && result == Err(client::Error::Deadline))
    {
        state.durable = false;
    }
    (state, result)
}
type Task = Pin<Box<dyn Future<Output = (State, Result<Json, client::Error>)> + Send + 'static>>;
pub(crate) struct Driver {
    state: Option<State>,
    task: Option<Task>,
    adapter: Adapter,
    mode: Option<Command>,
    last: Json,
    cancel_prepare: bool,
}
impl Driver {
    pub fn start(
        descriptor: Descriptor,
        setup_bytes: &[u8],
        contract: Contract,
    ) -> Result<Self, client::Error> {
        descriptor.policy.validate()?;
        if descriptor.abi_version != 1 || !descriptor.capabilities.validate() {
            return Err(client::Error::Policy);
        }
        let setup: Setup =
            serde_json::from_slice(setup_bytes).map_err(|_| client::Error::Identity)?;
        let raw: Json = serde_json::from_slice(setup_bytes).map_err(|_| client::Error::Identity)?;
        let context = Zeroizing::new(
            serde_json::to_vec(&raw["hostContext"]).map_err(|_| client::Error::Identity)?,
        );
        let (target, entry) = address(&contract)?;
        let mut runtime = host::Runtime::new(setup.host_context, &BTreeMap::new(), target, entry)
            .map_err(|_| client::Error::Identity)?;
        for stage in setup.stages {
            runtime.stage(stage).map_err(|_| client::Error::Identity)?;
        }
        runtime
            .execution_finished(true)
            .map_err(|_| client::Error::State)?;
        let policy = descriptor.policy.clone();
        Ok(Self::new(
            descriptor,
            State {
                policy,
                contract: Some(contract),
                runtime: Some(runtime),
                attempt: None,
                context,
                receipt: None,
                durable: false,
                cancelled: false,
            },
        ))
    }
    fn new(descriptor: Descriptor, mut state: State) -> Self {
        state.policy = descriptor.policy.clone();
        Self {
            state: Some(state),
            task: None,
            adapter: Adapter {
                mailbox: Arc::new(Mutex::new(Mailbox {
                    pending: None,
                    count: 0,
                })),
                capabilities: descriptor.capabilities,
                policy: descriptor.policy,
            },
            mode: None,
            last: json!({"status":"ready"}),
            cancel_prepare: false,
        }
    }
    pub fn recover(descriptor: Descriptor, context: &[u8]) -> Result<Self, client::Error> {
        descriptor.policy.validate()?;
        if descriptor.abi_version != 1 || !descriptor.capabilities.validate() {
            return Err(client::Error::Policy);
        }
        let _: host::Context =
            serde_json::from_slice(context).map_err(|_| client::Error::Identity)?;
        let policy = descriptor.policy.clone();
        let mut driver = Self::new(
            descriptor,
            State {
                policy,
                contract: None,
                runtime: None,
                attempt: None,
                context: Zeroizing::new(context.to_vec()),
                receipt: None,
                durable: false,
                cancelled: false,
            },
        );
        driver.command(Command::Reload)?;
        Ok(driver)
    }
    pub fn command(&mut self, command: Command) -> Result<(), client::Error> {
        if self.task.is_some() {
            if command == Command::Cancel && self.mode == Some(Command::Prepare) {
                self.cancel_prepare = true;
                if let Some(q) = self.request() {
                    self.complete(q.id, ServiceReply::Failure)?;
                }
                return Ok(());
            }
            return Err(client::Error::State);
        }
        let s = self.state.as_mut().ok_or(client::Error::State)?;
        if s.cancelled {
            return Err(client::Error::State);
        }
        if command == Command::Cancel
            && s.attempt
                .as_ref()
                .is_some_and(|a| !matches!(a.phase(), Ok(Phase::Prepared | Phase::Cancelled)))
        {
            return Err(client::Error::CancellationAfterBroadcast);
        }
        if command == Command::Prepare && s.contract.is_none() {
            return Err(client::Error::State);
        }
        if command == Command::Cancel && s.attempt.is_none() {
            s.runtime
                .as_mut()
                .ok_or(client::Error::State)?
                .cancel()
                .map_err(|_| client::Error::State)?;
            s.cancelled = true;
            self.last = json!({"status":"cancelled"});
            return Ok(());
        }
        if command == Command::Prepare && s.attempt.is_some() {
            return Err(client::Error::State);
        }
        if command != Command::Prepare && command != Command::Reload && s.attempt.is_none() {
            return Err(client::Error::State);
        }
        if let Some(attempt) = &s.attempt {
            let phase = attempt.phase()?;
            let allowed = match command {
                Command::Prepare => false,
                Command::Submit => {
                    matches!(phase, Phase::Prepared | Phase::Submitted | Phase::Uncertain)
                }
                Command::Observe => matches!(
                    phase,
                    Phase::Submitted
                        | Phase::Uncertain
                        | Phase::AwaitingCas
                        | Phase::Committed
                        | Phase::Conflicted
                ),
                Command::Commit => matches!(
                    phase,
                    Phase::AwaitingCas | Phase::Committed | Phase::Conflicted
                ),
                Command::Cancel => matches!(phase, Phase::Prepared | Phase::Cancelled),
                Command::Deadline => matches!(
                    phase,
                    Phase::Prepared | Phase::Submitted | Phase::Uncertain | Phase::Cancelled
                ),
                Command::Reload => true,
            };
            if !allowed {
                return Err(client::Error::State);
            }
        }
        let state = self.state.take().ok_or(client::Error::State)?;
        self.mode = Some(command);
        self.task = Some(Box::pin(step(state, command, self.adapter.clone())));
        Ok(())
    }
    pub fn poll(&mut self) -> Result<(), client::Error> {
        for _ in 0..3 {
            if self.cancel_prepare {
                if let Some(q) = self.request() {
                    self.complete(q.id, ServiceReply::Failure)?;
                }
            }
            let Some(task) = self.task.as_mut() else {
                break;
            };
            let waker = noop_waker();
            let mut context = Context::from_waker(&waker);
            match task.as_mut().poll(&mut context) {
                Poll::Ready((mut state, result)) => {
                    if self.cancel_prepare {
                        self.cancel_prepare = false;
                        // The last signing reply can win the race with cancellation.
                        // A newly bound attempt must complete SDK cancellation durably.
                        if state.attempt.is_some() {
                            self.mode = Some(Command::Cancel);
                            self.task =
                                Some(Box::pin(step(state, Command::Cancel, self.adapter.clone())));
                            continue;
                        }
                        if let Some(runtime) = state.runtime.as_mut() {
                            if runtime.cancel().is_err() {
                                self.last =
                                    json!({"status":"step_error","error":"nightlean_client_State"});
                                self.state = Some(state);
                                self.task = None;
                                self.mode = None;
                                break;
                            }
                        }
                        state.cancelled = true;
                        self.last = json!({"status":"cancelled","phase":"Cancelled"});
                    } else {
                        self.last = match result {
                            Ok(value) => value,
                            Err(error) => json!({"status":"step_error","error":error.to_string()}),
                        };
                    }
                    self.state = Some(state);
                    self.task = None;
                    self.mode = None;
                    break;
                }
                Poll::Pending => {
                    if !self.cancel_prepare {
                        break;
                    }
                }
            }
        }
        Ok(())
    }
    pub fn request(&self) -> Option<Arc<Request>> {
        self.adapter
            .mailbox
            .lock()
            .ok()?
            .pending
            .as_ref()
            .map(|p| p.request.clone())
    }
    pub fn complete(&self, id: u64, reply: ServiceReply) -> Result<(), client::Error> {
        let mut m = self
            .adapter
            .mailbox
            .lock()
            .map_err(|_| client::Error::State)?;
        let p = m.pending.as_ref().ok_or(client::Error::State)?;
        if p.request.id != id || !p.request.accepts(&reply) {
            return Err(client::Error::Identity);
        }
        let p = m.pending.take().ok_or(client::Error::State)?;
        p.sender.send(reply).map_err(|_| client::Error::State)
    }
    pub fn status(&self) -> Json {
        if let Some(request) = self.request() {
            return request.metadata();
        }
        let mut status = self.last.clone();
        status["abiVersion"] = json!(1);
        status["profile"] = json!(crate::profile::NAME);
        status["busy"] = json!(self.task.is_some());
        if let Some(state) = &self.state {
            if let Some(attempt) = &state.attempt {
                let t = attempt.transaction();
                status["phase"] = json!(format!("{:?}", attempt.phase().unwrap_or(Phase::Failed)));
                status["attemptId"] = json!(attempt.record().identity().attempt_id);
                status["transactionId"] = json!(t.transaction_id());
                status["contractAddress"] = json!(t.contract_address());
                status["event"] = json!(format!("{:?}", t.event()));
                status["durableAcknowledged"] = json!(state.durable);
                if let Some(cas) = attempt.record().cas_receipt() {
                    status["privateCommitted"] = json!(cas.committed);
                    status["privateRevision"] = json!(cas.revision);
                }
            } else if let Some(contract) = &state.contract {
                if let Ok((a, e)) = address(contract) {
                    status["contractAddress"] = json!(a);
                    status["entrypoint"] = json!(e)
                }
            }
            if state.cancelled {
                status["phase"] = json!("Cancelled")
            }
            if let Some(receipt) = &state.receipt {
                status["receipt"] = json!({"blockHash":receipt.block_hash,"height":receipt.height.to_string(),"finalizedHash":receipt.finalized_hash,"finalizedHeight":receipt.finalized_height.to_string(),"extrinsicHash":receipt.extrinsic_hash,"extrinsicIndex":receipt.extrinsic_index,"transactionId":receipt.transaction_id,"intentId":receipt.intent_id,"contractAddress":receipt.contract_address,"event":format!("{:?}",receipt.event),"contractStateBytes":receipt.contract_state.len(),"contractStateSha256":crate::artifacts::digest(&receipt.contract_state)})
            }
        }
        status
    }
    pub fn detachable(&self) -> bool {
        if self.task.is_some() {
            return false;
        }
        self.state
            .as_ref()
            .is_none_or(|s| s.attempt.is_none() || s.durable)
    }
    pub fn transaction(&self) -> Result<Vec<u8>, client::Error> {
        Ok(self
            .state
            .as_ref()
            .and_then(|s| s.attempt.as_ref())
            .ok_or(client::Error::State)?
            .transaction()
            .bytes()
            .to_vec())
    }
    pub fn receipt_state(&self) -> Result<Vec<u8>, client::Error> {
        Ok(self
            .state
            .as_ref()
            .and_then(|s| s.receipt.as_ref())
            .ok_or(client::Error::State)?
            .contract_state
            .clone())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn new_wire_identities_and_budgets_are_lossless_decimal_strings() {
        let policy = NetworkPolicy {
            network_id: "undeployed".into(),
            genesis: "8".repeat(64),
            spec_version: 1,
            transaction_version: 4,
            profile: crate::profile::NAME.into(),
            max_dust: 1,
        };
        let request = Request {
            id: 9_007_199_254_740_993,
            operation: "chain.snapshot.v1",
            capability: "chain".into(),
            schema: "native.snapshot.v1",
            policy,
            data: RequestData::Snapshot,
        };
        assert_eq!(request.metadata()["requestId"], "9007199254740993");
        let wire = json!({"abiVersion":1,"policy":{"networkId":"undeployed","genesis":"8".repeat(64),"specVersion":1,"transactionVersion":4,"profile":crate::profile::NAME,"maxDust":"340282366920938463463374607431768211455"},"capabilities":{"chain":"chain","funding":"wallet","signing":"signer","journal":"store"}});
        let descriptor: Descriptor = serde_json::from_value(wire.clone()).unwrap();
        assert_eq!(descriptor.policy.max_dust, u128::MAX);
        for value in [
            json!(1),
            json!("01"),
            json!("-1"),
            json!("340282366920938463463374607431768211456"),
        ] {
            let mut bad = wire.clone();
            bad["policy"]["maxDust"] = value;
            assert!(serde_json::from_value::<Descriptor>(bad).is_err());
        }
    }
    #[test]
    fn cancellation_racing_completed_preparation_retries_undurable_terminal_record() {
        let (attempt, runtime) = crate::client::tests::prepared_driver_fixture();
        let policy = attempt.transaction().policy().clone();
        let descriptor = Descriptor {
            abi_version: 1,
            policy: policy.clone(),
            capabilities: Capabilities {
                chain: "chain".into(),
                funding: "wallet".into(),
                signing: "signer".into(),
                journal: "store".into(),
            },
        };
        let state = State {
            policy,
            contract: None,
            runtime: Some(runtime),
            attempt: Some(attempt),
            context: Zeroizing::new(Vec::new()),
            receipt: None,
            durable: false,
            cancelled: false,
        };
        let mut driver = Driver::new(descriptor, state);
        let state = driver.state.take().unwrap();
        driver.task = Some(Box::pin(futures::future::ready((
            state,
            Ok(json!({"status":"step_done"})),
        ))));
        driver.mode = Some(Command::Prepare);
        driver.command(Command::Cancel).unwrap();
        driver.poll().unwrap();
        let request = driver.request().unwrap();
        assert!(matches!(request.data, RequestData::Persist { .. }));
        assert!(!driver.detachable());
        driver.complete(request.id, ServiceReply::Failure).unwrap();
        driver.poll().unwrap();
        assert_eq!(driver.status()["phase"], "Cancelled");
        assert_eq!(driver.status()["durableAcknowledged"], false);
        assert!(!driver.detachable());
        assert!(driver.command(Command::Submit).is_err());
        driver.command(Command::Cancel).unwrap();
        driver.poll().unwrap();
        let request = driver.request().unwrap();
        let RequestData::Persist { record, .. } = &request.data else {
            panic!("cancellation must only persist")
        };
        let ack = StoreAcknowledgement {
            identity: record.identity().clone(),
            record_sha256: crate::artifacts::digest(&record.private_bytes().unwrap()),
            revision: 1,
        };
        driver
            .complete(request.id, ServiceReply::Persisted(ack))
            .unwrap();
        driver.poll().unwrap();
        assert_eq!(driver.status()["phase"], "Cancelled");
        assert_eq!(driver.status()["durableAcknowledged"], true);
        assert!(driver.detachable());
        assert!(driver.request().is_none());
    }
}
