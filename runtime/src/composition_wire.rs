use crate::{Db, assembly::CompositionOffer};
use anyhow::{Result, ensure};
use base_crypto::{hash::HashOutput, time::Timestamp};
use coin_structure::{
    coin::{Commitment, PublicAddress, TokenType},
    contract::ContractAddress,
};
use ledger::construct::PreTranscript;
use onchain_runtime::{
    context::{CallContext, QueryContext},
    ops::Op,
    result_mode::ResultModeVerify,
    state::{ChargedState, EntryPointBuf},
    transcript::{MAX_CALL_PUBLIC_INPUTS, Transcript},
};
use serialize::{
    Deserializable, Serializable, Tagged, tagged_deserialize, tagged_serialize,
    tagged_serialized_size,
};
use storage::storage::{HashMap, Map};
use transient_crypto::{commitment::Pedersen, curve::Fr};

pub(crate) const MAX_OFFER_BYTES: usize = 4 * 1024 * 1024;
pub(crate) const MAX_DRAFT_BYTES: usize = 16 * 1024 * 1024;
pub(crate) const MAX_DRAFT_CALLS: usize = 64;

#[derive(Serializable)]
#[tag = "noctium-composition-draft[v1]"]
pub(crate) struct PublicDraft {
    pub profile: String,
    pub network_id: String,
    pub ttl: u64,
    pub binding: Pedersen,
    pub offers: Vec<Vec<u8>>,
    pub calls_sha256: [u8; 32],
}

// CallContext's JSON representation has object keys that cannot encode nonempty balances.
#[derive(PartialEq, Eq, Serializable)]
#[tag = "noctium-composition-context[v1]"]
pub(crate) struct PublicContext {
    own_address: ContractAddress,
    tblock: Timestamp,
    tblock_err: u32,
    parent_block_hash: HashOutput,
    caller: Option<PublicAddress>,
    balance: HashMap<TokenType, u128, Db>,
    com_indices: Map<Commitment, u64, Db>,
    last_block_time: Timestamp,
}

impl From<&CallContext<Db>> for PublicContext {
    fn from(value: &CallContext<Db>) -> Self {
        Self {
            own_address: value.own_address,
            tblock: value.tblock,
            tblock_err: value.tblock_err,
            parent_block_hash: value.parent_block_hash,
            caller: value.caller,
            balance: value.balance.clone(),
            com_indices: value.com_indices.clone(),
            last_block_time: value.last_block_time,
        }
    }
}

impl From<PublicContext> for CallContext<Db> {
    fn from(value: PublicContext) -> Self {
        Self {
            own_address: value.own_address,
            tblock: value.tblock,
            tblock_err: value.tblock_err,
            parent_block_hash: value.parent_block_hash,
            caller: value.caller,
            balance: value.balance,
            com_indices: value.com_indices,
            last_block_time: value.last_block_time,
        }
    }
}

#[derive(Serializable)]
#[tag = "noctium-composition-offer[v1]"]
struct PublicOffer {
    profile: String,
    address: ContractAddress,
    entry_point: EntryPointBuf,
    commitment: Fr,
    state: ChargedState<Db>,
    context: PublicContext,
    program: Vec<Op<ResultModeVerify, Db>>,
    activity: Vec<Option<u32>>,
}

impl PublicOffer {
    fn validate(&self) -> Result<()> {
        ensure!(
            !self.entry_point.0.is_empty() && std::str::from_utf8(&self.entry_point.0).is_ok(),
            "invalid composition entrypoint"
        );
        let checkpoints = self
            .program
            .iter()
            .filter(|op| matches!(op, Op::Ckpt))
            .count();
        // The native partitioner can replay one prefix per checkpoint.
        ensure!(
            self.program
                .len()
                .saturating_mul(checkpoints.saturating_add(1))
                <= MAX_CALL_PUBLIC_INPUTS,
            "composition offer replay limit"
        );
        let skips = self
            .activity
            .iter()
            .flatten()
            .fold(0usize, |total, skip| total.saturating_add(*skip as usize));
        let transcript = Transcript::<Db> {
            gas: Default::default(),
            effects: Default::default(),
            program: self.program.clone().into(),
            version: None,
        };
        ensure!(
            self.activity.iter().filter(|item| item.is_none()).count() == self.program.len()
                && self.activity.iter().flatten().all(|&skip| skip != 0)
                && transcript
                    .public_inputs_len()
                    .saturating_add(skips)
                    .saturating_add(2)
                    <= MAX_CALL_PUBLIC_INPUTS,
            "invalid composition activity schedule"
        );
        Ok(())
    }
}

pub(crate) fn encode<T: Serializable + Tagged>(value: &T, limit: usize) -> Result<Vec<u8>> {
    ensure!(
        tagged_serialized_size(value) <= limit,
        "public composition byte limit"
    );
    let mut bytes = Vec::new();
    tagged_serialize(value, &mut bytes)?;
    ensure!(bytes.len() <= limit, "public composition byte limit");
    Ok(bytes)
}

pub(crate) fn decode<T: Deserializable + Serializable + Tagged>(
    bytes: &[u8],
    limit: usize,
) -> Result<T> {
    ensure!(
        !bytes.is_empty() && bytes.len() <= limit,
        "public composition byte limit"
    );
    let decoded = tagged_deserialize(bytes)?;
    ensure!(
        encode(&decoded, limit)? == bytes,
        "noncanonical public composition bytes"
    );
    Ok(decoded)
}

impl CompositionOffer {
    /// Encode a checked offer as canonical, profile-scoped public bytes.
    pub fn public_bytes(&self) -> Result<Vec<u8>> {
        let pre = &self.pre_transcript;
        let wire = PublicOffer {
            profile: crate::profile::NAME.into(),
            address: pre.context.address,
            entry_point: self.entry_point.clone(),
            commitment: self.commitment(),
            state: pre.context.state.clone(),
            context: (&pre.context.call_context).into(),
            program: pre.program.clone(),
            activity: self
                .activity
                .iter()
                .map(|entry| entry.map(u32::try_from).transpose())
                .collect::<std::result::Result<Vec<_>, _>>()?,
        };
        wire.validate()?;
        encode(&wire, MAX_OFFER_BYTES)
    }

    /// Import public execution data supplied through the application's authenticated channel.
    /// Proof and ledger verification still establish validity of the resulting call.
    pub fn from_public_bytes(bytes: &[u8]) -> Result<Self> {
        let offer: PublicOffer = decode(bytes, MAX_OFFER_BYTES)?;
        ensure!(
            offer.profile == crate::profile::NAME,
            "composition offer profile mismatch"
        );
        offer.validate()?;
        let mut context = QueryContext::new(offer.state, offer.address);
        context.call_context = offer.context.into();
        Ok(Self {
            pre_transcript: PreTranscript {
                context,
                program: offer.program,
                comm_comm: Some(offer.commitment),
            },
            entry_point: offer.entry_point,
            activity: offer
                .activity
                .into_iter()
                .map(|entry| entry.map(|n| n as usize))
                .collect(),
        })
    }
}
