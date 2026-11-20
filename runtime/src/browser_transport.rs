//! Bounded browser host replies. The native driver owns transaction and receipt validation.
use crate::{
    client::{
        self, BoundTransaction, CasReceipt, ChainIdentity, FinalizedReceipt, JournalIdentity,
        NetworkPolicy, Observation, PublicTransactionReference, Snapshot, StoreAcknowledgement,
        StoredRecord, Submission,
    },
    witness_execution::{Error, Result, WitnessClientReply},
};
use serde::{Deserialize, Serialize};
use serialize::{Deserializable, Serializable, Tagged, tagged_deserialize, tagged_serialize};
use zeroize::Zeroizing;

const MAX_TRANSACTION: usize = 4 * 1024 * 1024;
const MAX_CONTRACT_STATE: usize = 1024 * 1024;
const MAX_LEDGER_STATE: usize = 32 * 1024 * 1024;
const MAX_BLOCK_CONTEXT: usize = 4096;
const MAX_RECORD: usize = 32 * 1024 * 1024;
pub const MAX_REPLY_BYTES: usize = 2 * MAX_RECORD + 1024 * 1024;

fn invalid() -> Error {
    Error::Client(client::Error::InvalidTransaction)
}

fn decimal(input: &str) -> Result<u64> {
    input
        .parse::<u64>()
        .ok()
        .filter(|value| value.to_string() == input)
        .ok_or_else(invalid)
}

fn hex_bytes(input: &str, max: usize) -> Result<Zeroizing<Vec<u8>>> {
    if input.len() > max * 2 {
        return Err(Error::ResourceLimit);
    }
    if input.is_empty()
        || !input
            .bytes()
            .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
    {
        return Err(invalid());
    }
    hex::decode(input)
        .map(Zeroizing::new)
        .map_err(|_| invalid())
}

fn read_tagged<T: Deserializable + Tagged>(input: &str, max: usize) -> Result<T> {
    let bytes = hex_bytes(input, max)?;
    let mut remaining = bytes.as_slice();
    let value = tagged_deserialize(&mut remaining).map_err(|_| invalid())?;
    if !remaining.is_empty() {
        return Err(invalid());
    }
    Ok(value)
}

fn write_tagged<T: Serializable + Tagged>(value: &T, max: usize) -> Result<String> {
    let mut bytes = Vec::new();
    tagged_serialize(value, &mut bytes).map_err(|_| invalid())?;
    if bytes.len() > max {
        return Err(Error::ResourceLimit);
    }
    Ok(hex::encode(bytes))
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct SnapshotWire {
    chain: ChainIdentity,
    finalized_hash: String,
    height: String,
    state: String,
    block: String,
}

pub fn encode_snapshot(snapshot: &Snapshot) -> Result<SnapshotWire> {
    Ok(SnapshotWire {
        chain: snapshot.chain.clone(),
        finalized_hash: snapshot.finalized_hash.clone(),
        height: snapshot.height.to_string(),
        state: write_tagged(&snapshot.state, MAX_LEDGER_STATE)?,
        block: write_tagged(&snapshot.block, MAX_BLOCK_CONTEXT)?,
    })
}

impl SnapshotWire {
    fn into_snapshot(self) -> Result<Snapshot> {
        Ok(Snapshot {
            chain: self.chain,
            finalized_hash: self.finalized_hash,
            height: decimal(&self.height)?,
            state: read_tagged(&self.state, MAX_LEDGER_STATE)?,
            block: read_tagged(&self.block, MAX_BLOCK_CONTEXT)?,
        })
    }
}

/// Read-only transport binding. Broadcast requires a separately authorized provider.
#[derive(Serialize, Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct TransactionRequest {
    transaction: String,
    after_height: String,
    expected_state: String,
}

pub fn transaction_request(transaction: &BoundTransaction) -> TransactionRequest {
    TransactionRequest {
        transaction: hex::encode(transaction.bytes()),
        after_height: transaction.after_height().to_string(),
        expected_state: hex::encode(transaction.expected_state()),
    }
}

impl TransactionRequest {
    pub fn reference(&self, policy: &NetworkPolicy) -> Result<PublicTransactionReference> {
        PublicTransactionReference::from_bytes(
            policy.clone(),
            &self.bytes()?,
            decimal(&self.after_height)?,
            &hex_bytes(&self.expected_state, MAX_CONTRACT_STATE)?,
        )
        .map_err(Error::Client)
    }

    pub fn bytes(&self) -> Result<Zeroizing<Vec<u8>>> {
        hex_bytes(&self.transaction, MAX_TRANSACTION)
    }
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum SubmissionStatus {
    Broadcast,
    Rejected,
    Uncertain,
}

#[derive(Deserialize)]
#[serde(rename_all = "lowercase")]
enum ObservationStatus {
    Pending,
    Rejected,
    Finalized,
}

#[derive(Deserialize)]
#[serde(
    tag = "kind",
    rename_all = "camelCase",
    rename_all_fields = "camelCase",
    deny_unknown_fields
)]
enum Reply {
    Snapshot {
        snapshot: SnapshotWire,
    },
    Funded {
        transaction: String,
    },
    Signed {
        transaction: String,
    },
    Submitted {
        status: SubmissionStatus,
    },
    Observed {
        status: ObservationStatus,
        receipt: Option<FinalizedReceipt>,
    },
    Loaded {
        revision: String,
        record: String,
    },
    Persisted {
        identity: JournalIdentity,
        record_sha256: String,
        revision: String,
    },
    Cas {
        identity: JournalIdentity,
        revision: String,
        committed: bool,
    },
    Failure,
}

pub fn decode_reply(input: &[u8]) -> Result<WitnessClientReply> {
    if input.len() > MAX_REPLY_BYTES {
        return Err(Error::ResourceLimit);
    }
    let reply: Reply = serde_json::from_slice(input).map_err(|_| invalid())?;
    Ok(match reply {
        Reply::Snapshot { snapshot } => WitnessClientReply::Snapshot(snapshot.into_snapshot()?),
        Reply::Funded { transaction } => {
            WitnessClientReply::Funded(read_tagged(&Zeroizing::new(transaction), MAX_TRANSACTION)?)
        }
        Reply::Signed { transaction } => {
            WitnessClientReply::Signed(read_tagged(&transaction, MAX_TRANSACTION)?)
        }
        Reply::Submitted { status } => WitnessClientReply::Submitted(match status {
            SubmissionStatus::Broadcast => Submission::Broadcast,
            SubmissionStatus::Rejected => Submission::Rejected,
            SubmissionStatus::Uncertain => Submission::Uncertain,
        }),
        Reply::Observed { status, receipt } => {
            WitnessClientReply::Observed(match (status, receipt) {
                (ObservationStatus::Pending, None) => Observation::Pending,
                (ObservationStatus::Rejected, None) => Observation::Rejected,
                (ObservationStatus::Finalized, Some(receipt)) => Observation::Finalized(receipt),
                _ => return Err(invalid()),
            })
        }
        Reply::Loaded { revision, record } => WitnessClientReply::Loaded(StoredRecord {
            private_bytes: hex_bytes(&Zeroizing::new(record), MAX_RECORD)?,
            revision: decimal(&revision)?,
        }),
        Reply::Persisted {
            identity,
            record_sha256,
            revision,
        } => WitnessClientReply::Persisted(StoreAcknowledgement {
            identity,
            record_sha256,
            revision: decimal(&revision)?,
        }),
        Reply::Cas {
            identity,
            revision,
            committed,
        } => WitnessClientReply::Cas(CasReceipt {
            identity,
            revision,
            committed,
        }),
        Reply::Failure => WitnessClientReply::Failure,
    })
}
