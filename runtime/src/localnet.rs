//! Opt-in host adapter. Every endpoint, network policy, deadline and wallet seed is explicit.
#[path = "localnet_store.rs"]
pub mod journal;
use crate::{
    Db,
    client::{ChainIdentity, NetworkPolicy, Snapshot},
};
use base_crypto::{
    cost_model::{FixedPoint, SyntheticCost},
    hash::HashOutput,
    time::Timestamp,
};
use frame_metadata::{RuntimeMetadata, RuntimeMetadataPrefixed, v16::RuntimeMetadataV16};
use ledger::{
    dust::{DustLocalState, DustSecretKey},
    semantics::{TransactionContext, TransactionResult},
    structure::{LedgerState, SystemTransaction},
    verify::WellFormedStrictness,
};
use onchain_runtime::context::BlockContext;
use parity_scale_codec::{Compact, Decode, Encode};
use reqwest::blocking::Client;
use scale_info::{PortableRegistry, TypeDef, TypeDefPrimitive};
use scale_value::{Composite, Value as ScaleValue, ValueDef};
use serde_json::{Value as Json, json};
use serialize::{Deserializable, Serializable, Tagged, tagged_deserialize};
use std::{cell::RefCell, io::Read, time::Duration};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    Policy,
    Transport,
    Limit,
    Response,
    Network,
    Metadata,
    State,
    Replay,
    Proof,
    Storage,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "nightlean_localnet_{self:?}")
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;
fn check(value: bool, error: Error) -> Result<()> {
    if value { Ok(()) } else { Err(error) }
}
fn hex_bytes(value: &Json) -> Result<Vec<u8>> {
    hex::decode(
        value
            .as_str()
            .ok_or(Error::Response)?
            .strip_prefix("0x")
            .unwrap_or(value.as_str().ok_or(Error::Response)?),
    )
    .map_err(|_| Error::Response)
}
fn hash_text(value: &Json) -> Result<String> {
    let bytes = hex_bytes(value)?;
    check(bytes.len() == 32, Error::Response)?;
    Ok(hex::encode(bytes))
}

pub struct Rpc {
    client: Client,
    endpoint: reqwest::Url,
    max_response: usize,
}
/// Read-only host-selected cache. The native provider checks its pinned official hashes.
/// Synchronous mode rejects missing files and never fetches from the supplied source URL.
pub struct ProofCache {
    provider: base_crypto::data_provider::MidnightDataProvider,
}
impl ProofCache {
    pub fn new(directory: std::path::PathBuf, parameter_source: reqwest::Url) -> Result<Self> {
        check(
            matches!(parameter_source.scheme(), "http" | "https"),
            Error::Policy,
        )?;
        Ok(Self {
            provider: base_crypto::data_provider::MidnightDataProvider {
                fetch_mode: base_crypto::data_provider::FetchMode::Synchronous,
                base_url: parameter_source,
                output_mode: base_crypto::data_provider::OutputMode::Log,
                expected_data: ledger::dust::DUST_EXPECTED_FILES.to_vec(),
                dir: directory,
            },
        })
    }
    async fn read(&self, path: &str, limit: usize) -> Result<Vec<u8>> {
        let file = self
            .provider
            .get_file(path, "native cache material missing")
            .await
            .map_err(|_| Error::Proof)?;
        let mut bytes = Vec::new();
        file.take(limit as u64 + 1)
            .read_to_end(&mut bytes)
            .map_err(|_| Error::Proof)?;
        check(bytes.len() <= limit, Error::Limit)?;
        Ok(bytes)
    }
    pub async fn dust(&self) -> Result<crate::funding::DustMaterial> {
        let mut values = Vec::new();
        for suffix in ["spend.prover", "spend.verifier", "spend.bzkir"] {
            let (path, _, _) = ledger::dust::DUST_EXPECTED_FILES
                .iter()
                .find(|(path, _, _)| path.ends_with(suffix))
                .ok_or(Error::Proof)?;
            values.push(self.read(path, 16 * 1024 * 1024).await?);
        }
        crate::funding::DustMaterial::from_bytes(&values[0], &values[1], &values[2])
            .map_err(|_| Error::Proof)
    }
    pub async fn parameters(&self, k: u8) -> Result<crate::proof::TrustedParameters> {
        check((1..=20).contains(&k), Error::Proof)?;
        let bytes = self
            .read(
                &base_crypto::data_provider::MidnightDataProvider::name_k(k),
                128 * 1024 * 1024,
            )
            .await?;
        use sha2::Digest;
        let digest = hex::encode(sha2::Sha256::digest(&bytes));
        crate::proof::TrustedParameters::from_bytes(&bytes, k, &digest).map_err(|_| Error::Proof)
    }
}
impl Rpc {
    pub fn new(endpoint: &str, timeout: Duration, max_response: usize) -> Result<Self> {
        let endpoint = reqwest::Url::parse(endpoint).map_err(|_| Error::Policy)?;
        check(
            matches!(endpoint.scheme(), "http" | "https")
                && endpoint.username().is_empty()
                && endpoint.password().is_none()
                && timeout >= Duration::from_millis(1)
                && timeout <= Duration::from_secs(120)
                && (1024..=64 * 1024 * 1024).contains(&max_response),
            Error::Policy,
        )?;
        let client = Client::builder()
            .no_proxy()
            .redirect(reqwest::redirect::Policy::none())
            .timeout(timeout)
            .build()
            .map_err(|_| Error::Transport)?;
        Ok(Self {
            client,
            endpoint,
            max_response,
        })
    }
    fn send(&self, body: &Json) -> Result<Json> {
        let response = self
            .client
            .post(self.endpoint.clone())
            .json(body)
            .send()
            .map_err(|_| Error::Transport)?
            .error_for_status()
            .map_err(|_| Error::Transport)?;
        if response
            .content_length()
            .is_some_and(|len| len > self.max_response as u64)
        {
            return Err(Error::Limit);
        }
        let mut bytes = Vec::new();
        response
            .take(self.max_response as u64 + 1)
            .read_to_end(&mut bytes)
            .map_err(|_| Error::Transport)?;
        check(bytes.len() <= self.max_response, Error::Limit)?;
        serde_json::from_slice(&bytes).map_err(|_| Error::Response)
    }
    pub fn call(&self, method: &str, params: Json) -> Result<Json> {
        let response =
            self.send(&json!({"jsonrpc":"2.0","id":1,"method":method,"params":params}))?;
        check(
            response["jsonrpc"] == "2.0" && response["id"] == 1 && response.get("error").is_none(),
            Error::Response,
        )?;
        response.get("result").cloned().ok_or(Error::Response)
    }
    fn batch(&self, calls: &[(String, Json)]) -> Result<Vec<Json>> {
        check(!calls.is_empty() && calls.len() <= 128, Error::Limit)?;
        let request = calls.iter().enumerate().map(|(id, (method, params))| json!({"jsonrpc":"2.0","id":id,"method":method,"params":params})).collect::<Vec<_>>();
        let response = self.send(&Json::Array(request))?;
        let rows = response.as_array().ok_or(Error::Response)?;
        check(rows.len() == calls.len(), Error::Response)?;
        let mut out = vec![None; calls.len()];
        for row in rows {
            let id = row["id"].as_u64().ok_or(Error::Response)? as usize;
            check(
                id < out.len()
                    && out[id].is_none()
                    && row["jsonrpc"] == "2.0"
                    && row.get("error").is_none(),
                Error::Response,
            )?;
            out[id] = Some(row.get("result").cloned().ok_or(Error::Response)?);
        }
        out.into_iter()
            .map(|row| row.ok_or(Error::Response))
            .collect()
    }
    pub fn chain_identity(&self, at: &str, profile: &str) -> Result<ChainIdentity> {
        let genesis = hash_text(&self.call("chain_getBlockHash", json!([0]))?)?;
        let runtime = self.call("state_getRuntimeVersion", json!([format!("0x{at}")]))?;
        check(runtime["specName"] == "midnight", Error::Network)?;
        let network = hex_bytes(&self.call(
            "state_call",
            json!(["MidnightRuntimeApi_get_network_id", "0x", format!("0x{at}")]),
        )?)?;
        let mut reader = network.as_slice();
        let network_id = String::decode(&mut reader).map_err(|_| Error::Response)?;
        check(reader.is_empty(), Error::Response)?;
        Ok(ChainIdentity {
            network_id,
            genesis,
            spec_version: runtime["specVersion"]
                .as_u64()
                .and_then(|n| u32::try_from(n).ok())
                .ok_or(Error::Response)?,
            transaction_version: runtime["transactionVersion"]
                .as_u64()
                .and_then(|n| u32::try_from(n).ok())
                .ok_or(Error::Response)?,
            profile: profile.into(),
        })
    }
    pub fn metadata(&self, at: &str) -> Result<Metadata> {
        let negotiated = hex_bytes(&self.call(
            "state_call",
            json!([
                "Metadata_metadata_at_version",
                "0x10000000",
                format!("0x{at}")
            ]),
        )?)?;
        let mut outer = negotiated.as_slice();
        check(
            u8::decode(&mut outer).map_err(|_| Error::Metadata)? == 1,
            Error::Metadata,
        )?;
        let length = Compact::<u32>::decode(&mut outer)
            .map_err(|_| Error::Metadata)?
            .0 as usize;
        check(
            length == outer.len() && length <= 2 * 1024 * 1024,
            Error::Metadata,
        )?;
        let RuntimeMetadataPrefixed(magic, metadata) =
            RuntimeMetadataPrefixed::decode(&mut outer).map_err(|_| Error::Metadata)?;
        check(
            magic == frame_metadata::META_RESERVED && outer.is_empty(),
            Error::Metadata,
        )?;
        let RuntimeMetadata::V16(metadata) = metadata else {
            return Err(Error::Metadata);
        };
        Metadata::new(metadata)
    }
}

pub struct Metadata {
    native: RuntimeMetadataV16,
    pub pallet: u8,
    pub call: u8,
    events_type: u32,
    fingerprint: Vec<u8>,
}
impl Metadata {
    fn variants(
        registry: &PortableRegistry,
        id: u32,
    ) -> Result<&scale_info::TypeDefVariant<scale_info::form::PortableForm>> {
        let ty = registry.resolve(id).ok_or(Error::Metadata)?;
        if let TypeDef::Variant(variants) = &ty.type_def {
            Ok(variants)
        } else {
            Err(Error::Metadata)
        }
    }
    fn bytes_type(registry: &PortableRegistry, id: u32, depth: usize) -> bool {
        if depth > 8 {
            return false;
        }
        let Some(ty) = registry.resolve(id) else {
            return false;
        };
        match &ty.type_def {
            TypeDef::Sequence(sequence) => registry
                .resolve(sequence.type_param.id)
                .is_some_and(|ty| ty.type_def == TypeDef::Primitive(TypeDefPrimitive::U8)),
            TypeDef::Composite(composite) if composite.fields.len() == 1 => {
                Self::bytes_type(registry, composite.fields[0].ty.id, depth + 1)
            }
            _ => false,
        }
    }
    pub fn new(native: RuntimeMetadataV16) -> Result<Self> {
        check(native.extrinsic.versions.contains(&4), Error::Metadata)?;
        let pallet = native
            .pallets
            .iter()
            .find(|p| p.name == "Midnight")
            .ok_or(Error::Metadata)?;
        let calls = Self::variants(
            &native.types,
            pallet.calls.as_ref().ok_or(Error::Metadata)?.ty.id,
        )?;
        let call = calls
            .variants
            .iter()
            .find(|c| c.name == "send_mn_transaction")
            .ok_or(Error::Metadata)?;
        check(
            call.fields.len() == 1
                && call.fields[0].name.as_deref() == Some("midnight_tx")
                && Self::bytes_type(&native.types, call.fields[0].ty.id, 0),
            Error::Metadata,
        )?;
        let system = native
            .pallets
            .iter()
            .find(|p| p.name == "System")
            .ok_or(Error::Metadata)?;
        let events = system
            .storage
            .as_ref()
            .ok_or(Error::Metadata)?
            .entries
            .iter()
            .find(|e| e.name == "Events")
            .ok_or(Error::Metadata)?;
        let frame_metadata::v14::StorageEntryType::Plain(events_type) = &events.ty else {
            return Err(Error::Metadata);
        };
        use sha2::Digest;
        let fingerprint = sha2::Sha256::digest(native.encode()).to_vec();
        let result = Self {
            fingerprint,
            pallet: pallet.index,
            call: call.index,
            events_type: events_type.id,
            native,
        };
        result.validate_events()?;
        Ok(result)
    }
    fn validate_events(&self) -> Result<()> {
        let pallet = self
            .native
            .pallets
            .iter()
            .find(|p| p.name == "Midnight")
            .ok_or(Error::Metadata)?;
        let events = Self::variants(
            &self.native.types,
            pallet.event.as_ref().ok_or(Error::Metadata)?.ty.id,
        )?;
        for name in [
            "ContractCall",
            "ContractDeploy",
            "TxApplied",
            "TxPartialSuccess",
        ] {
            check(
                events.variants.iter().any(|v| v.name == name),
                Error::Metadata,
            )?;
        }
        Ok(())
    }
    pub fn extrinsic(&self, native_transaction: &[u8]) -> Result<Vec<u8>> {
        check(
            !native_transaction.is_empty() && native_transaction.len() <= 4 * 1024 * 1024,
            Error::Limit,
        )?;
        let mut payload = vec![4, self.pallet, self.call];
        Compact(u32::try_from(native_transaction.len()).map_err(|_| Error::Limit)?)
            .encode_to(&mut payload);
        payload.extend_from_slice(native_transaction);
        let mut out = Compact(u32::try_from(payload.len()).map_err(|_| Error::Limit)?).encode();
        out.extend(payload);
        Ok(out)
    }
    pub fn events(&self, encoded: &[u8]) -> Result<scale_value::Value<u32>> {
        check(encoded.len() <= 4 * 1024 * 1024, Error::Limit)?;
        let mut reader = encoded;
        let events =
            scale_value::scale::decode_as_type(&mut reader, self.events_type, &self.native.types)
                .map_err(|_| Error::Metadata)?;
        check(reader.is_empty(), Error::Metadata)?;
        Ok(events)
    }
    fn call_value(&self, extrinsic: &[u8]) -> Result<Option<ScaleValue<u32>>> {
        let mut reader = extrinsic;
        let len = Compact::<u32>::decode(&mut reader)
            .map_err(|_| Error::Metadata)?
            .0 as usize;
        check(len == reader.len(), Error::Metadata)?;
        let version = u8::decode(&mut reader).map_err(|_| Error::Metadata)?;
        if version & 128 != 0 {
            return Ok(None);
        }
        check(
            (version == 4 || version == 5) && self.native.extrinsic.versions.contains(&version),
            Error::Metadata,
        )?;
        let value = scale_value::scale::decode_as_type(
            &mut reader,
            self.native.extrinsic.call_ty.id,
            &self.native.types,
        )
        .map_err(|_| Error::Metadata)?;
        check(reader.is_empty(), Error::Metadata)?;
        Ok(Some(value))
    }
}

fn field<'a>(value: &'a ScaleValue<u32>, name: &str) -> Option<&'a ScaleValue<u32>> {
    let fields = match &value.value {
        ValueDef::Composite(c) => c,
        ValueDef::Variant(v) => &v.values,
        _ => return None,
    };
    if let Composite::Named(values) = fields {
        if let Some((_, value)) = values.iter().find(|(key, _)| key == name) {
            return Some(value);
        }
    }
    if fields.len() == 1 {
        field(fields.values().next()?, name)
    } else {
        None
    }
}
fn variant(value: &ScaleValue<u32>) -> Result<(&str, &Composite<u32>)> {
    match &value.value {
        ValueDef::Variant(v) => Ok((&v.name, &v.values)),
        ValueDef::Composite(c) if c.len() == 1 => {
            variant(c.values().next().ok_or(Error::Metadata)?)
        }
        _ => Err(Error::Metadata),
    }
}
fn scale_bytes(value: &ScaleValue<u32>) -> Result<Vec<u8>> {
    let ValueDef::Composite(composite) = &value.value else {
        return Err(Error::Metadata);
    };
    if composite.len() == 1
        && matches!(
            composite.values().next().map(|v| &v.value),
            Some(ValueDef::Composite(_))
        )
    {
        return scale_bytes(composite.values().next().ok_or(Error::Metadata)?);
    }
    composite
        .values()
        .map(|v| {
            v.as_u128()
                .and_then(|n| u8::try_from(n).ok())
                .ok_or(Error::Metadata)
        })
        .collect()
}
fn phase(value: &ScaleValue<u32>) -> Result<u32> {
    let (name, values) = variant(value)?;
    match name {
        "ApplyExtrinsic" => values
            .values()
            .next()
            .and_then(ScaleValue::as_u128)
            .and_then(|n| u32::try_from(n).ok())
            .ok_or(Error::Metadata),
        "Initialization" => Ok(0),
        "Finalization" => Ok(u32::MAX),
        _ => Err(Error::Metadata),
    }
}
fn native_decode<T: Deserializable + Tagged>(bytes: &[u8]) -> Result<T> {
    tagged_deserialize(bytes).map_err(|_| Error::State)
}
fn native_bytes<T: Serializable>(value: &T) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    Serializable::serialize(value, &mut bytes).map_err(|_| Error::State)?;
    Ok(bytes)
}

enum ReplayTransaction {
    Native(Vec<u8>),
    System(Vec<u8>),
}
struct ReplayCache {
    state: LedgerState<Db>,
    dust: DustLocalState<Db>,
    height: u64,
    hash: String,
    block: BlockContext,
}
/// Development-node trust is explicit: finalized RPC history is replayed locally and
/// the resulting native ledger root must match the finalized runtime API root.
pub struct Node {
    rpc: Rpc,
    policy: NetworkPolicy,
    metadata: Metadata,
    runtime_code: String,
    cache: RefCell<Option<ReplayCache>>,
    dust_secret: RefCell<Option<DustSecretKey>>,
    max_replay_blocks: u64,
}
pub struct FinalizedContractState {
    pub chain: ChainIdentity,
    pub block_hash: String,
    pub height: u64,
    pub bytes: Vec<u8>,
}

impl Node {
    pub fn connect(
        endpoint: &str,
        policy: NetworkPolicy,
        timeout: Duration,
        max_response: usize,
        max_replay_blocks: u64,
    ) -> Result<Self> {
        policy.validate().map_err(|_| Error::Policy)?;
        check((1..=100_000).contains(&max_replay_blocks), Error::Policy)?;
        let rpc = Rpc::new(endpoint, timeout, max_response)?;
        check(
            matches!(
                rpc.endpoint.host_str(),
                Some("127.0.0.1" | "localhost" | "[::1]" | "::1")
            ),
            Error::Policy,
        )?;
        let at = hash_text(&rpc.call("chain_getFinalizedHead", json!([]))?)?;
        policy
            .check(&rpc.chain_identity(&at, &policy.profile)?)
            .map_err(|_| Error::Network)?;
        let metadata = rpc.metadata(&at)?;
        let runtime_code = hash_text(&rpc.call(
            "state_getStorageHash",
            json!(["0x3a636f6465", format!("0x{at}")]),
        )?)?;
        Ok(Self {
            rpc,
            policy,
            metadata,
            runtime_code,
            cache: RefCell::new(None),
            dust_secret: RefCell::new(None),
            max_replay_blocks,
        })
    }
    fn check_runtime(&self, at: &str) -> Result<()> {
        let code = hash_text(&self.rpc.call(
            "state_getStorageHash",
            json!(["0x3a636f6465", format!("0x{at}")]),
        )?)?;
        check(code == self.runtime_code, Error::Metadata)?;
        check(
            self.rpc.metadata(at)?.fingerprint == self.metadata.fingerprint,
            Error::Metadata,
        )
    }
    /// Public runtime identity, distinct from the selected contract compiler profile.
    pub fn runtime_fingerprint(&self) -> (String, String) {
        (
            self.runtime_code.clone(),
            hex::encode(&self.metadata.fingerprint),
        )
    }
    /// Public auditing reuses receipt verification without creating a submitting attempt.
    pub fn observe_public_reference(
        &self,
        reference: &crate::client::PublicTransactionReference,
    ) -> Result<Option<crate::client::FinalizedReceipt>> {
        self.receipt(&reference.bound_view())
    }
    pub fn finalized_contract_state(&self, address: &str) -> Result<FinalizedContractState> {
        check(
            address.len() == 64 && hex::decode(address).is_ok_and(|v| v.len() == 32),
            Error::Policy,
        )?;
        let hash = hash_text(&self.rpc.call("chain_getFinalizedHead", json!([]))?)?;
        let chain = self.rpc.chain_identity(&hash, &self.policy.profile)?;
        self.policy.check(&chain).map_err(|_| Error::Network)?;
        self.check_runtime(&hash)?;
        let header = self
            .rpc
            .call("chain_getHeader", json!([format!("0x{hash}")]))?;
        let height = u64::from_str_radix(
            header["number"]
                .as_str()
                .ok_or(Error::Response)?
                .trim_start_matches("0x"),
            16,
        )
        .map_err(|_| Error::Response)?;
        let bytes = hex_bytes(&self.rpc.call(
            "midnight_contractState",
            json!([address, format!("0x{hash}")]),
        )?)?;
        check(bytes.len() <= 1024 * 1024, Error::Limit)?;
        let state: onchain_runtime::state::ContractState<Db> = native_decode(&bytes)?;
        let mut canonical = Vec::new();
        serialize::tagged_serialize(&state, &mut canonical).map_err(|_| Error::State)?;
        check(bytes == canonical, Error::State)?;
        Ok(FinalizedContractState {
            chain,
            block_hash: hash,
            height,
            bytes,
        })
    }
    /// Read exact native parameters at a block linked to the captured finalized head.
    pub fn finalized_ledger_parameters_at(&self, block_hash: &str, height: u64) -> Result<Vec<u8>> {
        check(
            block_hash.len() == 64 && hex::decode(block_hash).is_ok_and(|v| v.len() == 32),
            Error::Policy,
        )?;
        let tip = hash_text(&self.rpc.call("chain_getFinalizedHead", json!([]))?)?;
        let chain = self.rpc.chain_identity(&tip, &self.policy.profile)?;
        self.policy.check(&chain).map_err(|_| Error::Network)?;
        self.check_runtime(&tip)?;
        let header = self
            .rpc
            .call("chain_getHeader", json!([format!("0x{tip}")]))?;
        let tip_height = u64::from_str_radix(
            header["number"]
                .as_str()
                .ok_or(Error::Response)?
                .trim_start_matches("0x"),
            16,
        )
        .map_err(|_| Error::Response)?;
        check(
            height <= tip_height && tip_height - height <= self.max_replay_blocks,
            Error::Limit,
        )?;
        let mut previous = None;
        for numbers in (height..=tip_height).collect::<Vec<_>>().chunks(40) {
            let hashes = self
                .rpc
                .batch(
                    &numbers
                        .iter()
                        .map(|n| ("chain_getBlockHash".into(), json!([n])))
                        .collect::<Vec<_>>(),
                )?
                .iter()
                .map(hash_text)
                .collect::<Result<Vec<_>>>()?;
            let rows = self.rpc.batch(
                &hashes
                    .iter()
                    .flat_map(|h| {
                        [
                            ("chain_getHeader".into(), json!([format!("0x{h}")])),
                            (
                                "state_getStorageHash".into(),
                                json!(["0x3a636f6465", format!("0x{h}")]),
                            ),
                        ]
                    })
                    .collect::<Vec<_>>(),
            )?;
            for (index, rows) in rows.chunks_exact(2).enumerate() {
                if previous.is_none() {
                    check(hashes[index] == block_hash, Error::Replay)?;
                }
                check(hash_text(&rows[1])? == self.runtime_code, Error::Metadata)?;
                let number = u64::from_str_radix(
                    rows[0]["number"]
                        .as_str()
                        .ok_or(Error::Response)?
                        .trim_start_matches("0x"),
                    16,
                )
                .map_err(|_| Error::Response)?;
                check(number == numbers[index], Error::Replay)?;
                validate_parent(previous.as_deref(), &hash_text(&rows[0]["parentHash"])?)?;
                previous = Some(hashes[index].clone());
            }
        }
        validate_finalized_tip(previous.as_deref(), &tip)?;
        self.check_runtime(block_hash)?;
        let bytes = hex_bytes(&self.rpc.call(
            "state_call",
            json!([
                "MidnightRuntimeApi_get_ledger_parameters",
                "0x",
                format!("0x{block_hash}")
            ]),
        )?)?;
        let mut reader = bytes.as_slice();
        check(
            u8::decode(&mut reader).map_err(|_| Error::State)? == 0,
            Error::State,
        )?;
        let value = Vec::<u8>::decode(&mut reader).map_err(|_| Error::State)?;
        check(
            reader.is_empty() && value.len() <= 1024 * 1024,
            Error::State,
        )?;
        let native: ledger::structure::LedgerParameters = native_decode(&value)?;
        let mut canonical = Vec::new();
        serialize::tagged_serialize(&native, &mut canonical).map_err(|_| Error::State)?;
        check(canonical == value, Error::State)?;
        Ok(value)
    }
    /// Attach only before the first sync. The seed never leaves this host adapter.
    pub fn attach_dust_seed(&self, root_seed: &[u8]) -> Result<()> {
        check(
            self.cache.borrow().is_none()
                && self.dust_secret.borrow().is_none()
                && matches!(root_seed.len(), 16 | 32),
            Error::Policy,
        )?;
        let path = "m/44'/2400'/0'/2/0".parse().map_err(|_| Error::Policy)?;
        let private = bip32::XPrv::derive_from_path(root_seed, &path).map_err(|_| Error::Policy)?;
        let derived = zeroize::Zeroizing::new(<[u8; 32]>::from(private.private_key().to_bytes()));
        *self.dust_secret.borrow_mut() = Some(DustSecretKey::derive_secret_key(&derived));
        Ok(())
    }
    fn transactions(
        &self,
        extrinsics: &[Json],
        events: Option<&ScaleValue<u32>>,
        genesis: bool,
    ) -> Result<(Timestamp, Vec<ReplayTransaction>)> {
        let mut timestamp = None;
        let mut transactions = Vec::new();
        for (index, encoded) in extrinsics.iter().enumerate() {
            let Some(call) = self.metadata.call_value(&hex_bytes(encoded)?)? else {
                continue;
            };
            let (pallet, values) = variant(&call)?;
            let nested = values.values().next().ok_or(Error::Metadata)?;
            let (name, _) = variant(nested)?;
            match (pallet, name) {
                ("Timestamp", "set") => {
                    check(timestamp.is_none(), Error::Replay)?;
                    timestamp = Some(
                        field(nested, "now")
                            .and_then(ScaleValue::as_u128)
                            .and_then(|n| u64::try_from(n).ok())
                            .ok_or(Error::Metadata)?
                            / 1000,
                    );
                }
                ("Midnight", "send_mn_transaction") => transactions.push((
                    index as u32,
                    ReplayTransaction::Native(scale_bytes(
                        field(nested, "midnight_tx").ok_or(Error::Metadata)?,
                    )?),
                )),
                ("MidnightSystem", "send_mn_system_transaction") if genesis => transactions.push((
                    index as u32,
                    ReplayTransaction::System(scale_bytes(
                        field(nested, "midnight_system_tx").ok_or(Error::Metadata)?,
                    )?),
                )),
                _ => {}
            }
        }
        if let Some(events) = events {
            let ValueDef::Composite(rows) = &events.value else {
                return Err(Error::Metadata);
            };
            for record in rows.values() {
                let event = field(record, "event").ok_or(Error::Metadata)?;
                let (pallet, values) = variant(event)?;
                let nested = values.values().next().ok_or(Error::Metadata)?;
                let (name, _) = variant(nested)?;
                if pallet == "MidnightSystem" && name == "SystemTransactionApplied" {
                    let order = phase(field(record, "phase").ok_or(Error::Metadata)?)?;
                    let tx = scale_bytes(
                        field(nested, "serialized_system_transaction").ok_or(Error::Metadata)?,
                    )?;
                    transactions.push((order, ReplayTransaction::System(tx)));
                }
            }
        }
        transactions.sort_by_key(|(index, _)| *index);
        Ok((
            Timestamp::from_secs(timestamp.unwrap_or(0)),
            transactions.into_iter().map(|(_, tx)| tx).collect(),
        ))
    }
    fn apply_block(
        &self,
        cache: &mut ReplayCache,
        block: BlockContext,
        transactions: Vec<ReplayTransaction>,
    ) -> Result<()> {
        let mut cost = SyntheticCost::ZERO;
        for transaction in transactions {
            let (next, events, spent) = match transaction {
                ReplayTransaction::System(bytes) => {
                    let tx: SystemTransaction = native_decode(&bytes)?;
                    let spent = tx.cost(&cache.state.parameters);
                    let (state, events) = cache
                        .state
                        .apply_system_tx(&tx, block.tblock)
                        .map_err(|_| Error::Replay)?;
                    (state, events, spent)
                }
                ReplayTransaction::Native(bytes) => {
                    let tx: crate::funding::SealedTransaction = native_decode(&bytes)?;
                    let context = TransactionContext {
                        ref_state: cache.state.clone(),
                        block_context: block.clone(),
                        whitelist: None,
                    };
                    let mut strictness = WellFormedStrictness::default();
                    // Finalized historical proofs were checked by the trusted node. The final
                    // native state-root comparison authenticates this bounded replay result.
                    strictness.verify_native_proofs = false;
                    strictness.verify_contract_proofs = false;
                    strictness.verify_signatures = false;
                    strictness.enforce_balancing = false;
                    let Ok(verified) =
                        tx.erase_proofs()
                            .well_formed(&cache.state, strictness, block.tblock)
                    else {
                        continue;
                    };
                    let spent = tx
                        .cost(&cache.state.parameters, false)
                        .map_err(|_| Error::Replay)?;
                    let (state, outcome) = cache.state.apply(&verified, &context);
                    let events = match outcome {
                        TransactionResult::Success(events)
                        | TransactionResult::PartialSuccess(_, events) => events,
                        TransactionResult::Failure(_) => Vec::new(),
                    };
                    (state, events, spent)
                }
            };
            cost = cost + spent;
            cache.state = next;
            if let Some(secret) = self.dust_secret.borrow().as_ref() {
                cache.dust = cache
                    .dust
                    .replay_events(secret, events.iter())
                    .map_err(|_| Error::Replay)?;
            }
        }
        let normalized = cost
            .normalize(cache.state.parameters.limits.block_limits)
            .ok_or(Error::Replay)?;
        let fullness = FixedPoint::max(
            FixedPoint::max(normalized.read_time, normalized.compute_time),
            FixedPoint::max(
                normalized.block_usage,
                FixedPoint::max(normalized.bytes_written, normalized.bytes_churned),
            ),
        );
        cache.state = cache
            .state
            .post_block_update(block.tblock, normalized, fullness)
            .map_err(|_| Error::Replay)?;
        cache.dust = cache.dust.process_ttls(block.tblock);
        cache.block = block;
        Ok(())
    }
    pub fn sync(&self) -> Result<Snapshot> {
        let final_hash = hash_text(&self.rpc.call("chain_getFinalizedHead", json!([]))?)?;
        let identity = self.rpc.chain_identity(&final_hash, &self.policy.profile)?;
        self.policy.check(&identity).map_err(|_| Error::Network)?;
        self.check_runtime(&final_hash)?;
        let header = self
            .rpc
            .call("chain_getHeader", json!([format!("0x{final_hash}")]))?;
        let height = u64::from_str_radix(
            header["number"]
                .as_str()
                .ok_or(Error::Response)?
                .trim_start_matches("0x"),
            16,
        )
        .map_err(|_| Error::Response)?;
        check(height <= self.max_replay_blocks, Error::Limit)?;
        let mut cache = self.cache.borrow_mut();
        if cache.is_none() {
            self.check_runtime(&self.policy.genesis)?;
            let properties = self.rpc.call("system_properties", json!([]))?;
            let initial: LedgerState<Db> =
                native_decode(&hex_bytes(&properties["genesis_state"])?)?;
            check(initial.network_id == self.policy.network_id, Error::Network)?;
            let genesis = properties["genesis_extrinsics"]
                .as_array()
                .ok_or(Error::Response)?;
            let (time, transactions) = self.transactions(genesis, None, true)?;
            let mut replay = ReplayCache {
                dust: DustLocalState::new(initial.parameters.dust),
                state: LedgerState::new(self.policy.network_id.clone()),
                height: 0,
                hash: self.policy.genesis.clone(),
                block: BlockContext::default(),
            };
            self.apply_block(
                &mut replay,
                BlockContext {
                    tblock: time,
                    ..Default::default()
                },
                transactions,
            )?;
            replay.state = initial;
            *cache = Some(replay);
        }
        let replay = cache.as_mut().ok_or(Error::State)?;
        check(height >= replay.height, Error::Replay)?;
        for heights in ((replay.height + 1)..=height)
            .collect::<Vec<_>>()
            .chunks(40)
        {
            let requests: Vec<_> = heights
                .iter()
                .map(|number| ("chain_getBlockHash".into(), json!([number])))
                .collect();
            let hashes = self
                .rpc
                .batch(&requests)?
                .iter()
                .map(hash_text)
                .collect::<Result<Vec<_>>>()?;
            let requests: Vec<_> = hashes.iter().flat_map(|hash| [("chain_getBlock".into(), json!([format!("0x{hash}")])), ("state_getStorage".into(), json!(["0x26aa394eea5630e07c48ae0c9558cef780d41e5e16056765bc8461851072c9d7",format!("0x{hash}")])), ("state_getStorageHash".into(),json!(["0x3a636f6465",format!("0x{hash}")]))]).collect();
            let rows = self.rpc.batch(&requests)?;
            for (index, hash) in hashes.iter().enumerate() {
                check(
                    hash_text(&rows[index * 3 + 2])? == self.runtime_code,
                    Error::Metadata,
                )?;
                let block = &rows[index * 3]["block"];
                check(
                    u64::from_str_radix(
                        block["header"]["number"]
                            .as_str()
                            .ok_or(Error::Response)?
                            .trim_start_matches("0x"),
                        16,
                    )
                    .map_err(|_| Error::Response)?
                        == heights[index],
                    Error::Replay,
                )?;
                check(
                    hash_text(&block["header"]["parentHash"])? == replay.hash,
                    Error::Replay,
                )?;
                let events = self.metadata.events(&hex_bytes(&rows[index * 3 + 1])?)?;
                let (time, transactions) = self.transactions(
                    block["extrinsics"].as_array().ok_or(Error::Response)?,
                    Some(&events),
                    false,
                )?;
                let context = BlockContext {
                    tblock: time,
                    tblock_err: 30,
                    parent_block_hash: HashOutput(
                        hex::decode(&replay.hash)
                            .map_err(|_| Error::Response)?
                            .try_into()
                            .map_err(|_| Error::Response)?,
                    ),
                    last_block_time: replay.block.tblock,
                };
                self.apply_block(replay, context, transactions)?;
                replay.height = heights[index];
                replay.hash = hash.clone();
            }
        }
        check(replay.hash == final_hash, Error::Replay)?;
        let raw_root = hex_bytes(&self.rpc.call(
            "state_call",
            json!([
                "MidnightRuntimeApi_get_ledger_state_root",
                "0x",
                format!("0x{final_hash}")
            ]),
        )?)?;
        let mut reader = raw_root.as_slice();
        check(
            u8::decode(&mut reader).map_err(|_| Error::State)? == 0,
            Error::State,
        )?;
        let root = Vec::<u8>::decode(&mut reader).map_err(|_| Error::State)?;
        check(reader.is_empty(), Error::State)?;
        let stored = storage::storage::default_storage::<Db>()
            .arena
            .alloc(replay.state.clone());
        check(native_bytes(&stored.as_typed_key())? == root, Error::Replay)?;
        Ok(Snapshot {
            chain: identity,
            finalized_hash: final_hash,
            height,
            state: replay.state.clone(),
            block: replay.block.clone(),
        })
    }
    fn receipt(
        &self,
        transaction: &crate::client::BoundTransaction,
    ) -> Result<Option<crate::client::FinalizedReceipt>> {
        transaction
            .policy()
            .check(&self.rpc.chain_identity(
                &hash_text(&self.rpc.call("chain_getFinalizedHead", json!([]))?)?,
                &self.policy.profile,
            )?)
            .map_err(|_| Error::Network)?;
        let final_hash = hash_text(&self.rpc.call("chain_getFinalizedHead", json!([]))?)?;
        let header = self
            .rpc
            .call("chain_getHeader", json!([format!("0x{final_hash}")]))?;
        let height = u64::from_str_radix(
            header["number"]
                .as_str()
                .ok_or(Error::Response)?
                .trim_start_matches("0x"),
            16,
        )
        .map_err(|_| Error::Response)?;
        check(
            height.saturating_sub(transaction.after_height()) <= self.max_replay_blocks,
            Error::Limit,
        )?;
        self.check_runtime(&final_hash)?;
        let expected = self.metadata.extrinsic(transaction.bytes())?;
        let mut previous = None;
        let mut found = None;
        for numbers in ((transaction.after_height() + 1)..=height)
            .collect::<Vec<_>>()
            .chunks(64)
        {
            let queries: Vec<_> = numbers
                .iter()
                .map(|n| ("chain_getBlockHash".into(), json!([n])))
                .collect();
            let hashes = self
                .rpc
                .batch(&queries)?
                .iter()
                .map(hash_text)
                .collect::<Result<Vec<_>>>()?;
            let blocks = self.rpc.batch(
                &hashes
                    .iter()
                    .flat_map(|h| {
                        [
                            ("chain_getBlock".into(), json!([format!("0x{h}")])),
                            (
                                "state_getStorageHash".into(),
                                json!(["0x3a636f6465", format!("0x{h}")]),
                            ),
                        ]
                    })
                    .collect::<Vec<_>>(),
            )?;
            for (offset, rows) in blocks.chunks_exact(2).enumerate() {
                check(hash_text(&rows[1])? == self.runtime_code, Error::Metadata)?;
                let block = &rows[0];
                let header_number = u64::from_str_radix(
                    block["block"]["header"]["number"]
                        .as_str()
                        .ok_or(Error::Response)?
                        .trim_start_matches("0x"),
                    16,
                )
                .map_err(|_| Error::Response)?;
                check(header_number == numbers[offset], Error::Replay)?;
                let parent = hash_text(&block["block"]["header"]["parentHash"])?;
                validate_parent(previous.as_deref(), &parent)?;
                previous = Some(hashes[offset].clone());
                let Some(index) = block["block"]["extrinsics"]
                    .as_array()
                    .ok_or(Error::Response)?
                    .iter()
                    .position(|e| hex_bytes(e).is_ok_and(|bytes| bytes == expected))
                else {
                    continue;
                };
                let encoded = self.rpc.call(
                    "state_getStorage",
                    json!([
                        "0x26aa394eea5630e07c48ae0c9558cef780d41e5e16056765bc8461851072c9d7",
                        format!("0x{}", hashes[offset])
                    ]),
                )?;
                let decoded = self.metadata.events(&hex_bytes(&encoded)?)?;
                let ValueDef::Composite(rows) = &decoded.value else {
                    return Err(Error::Metadata);
                };
                let mut applied = 0;
                let mut contract = 0;
                for row in rows.values() {
                    let (phase_name, phase_fields) =
                        variant(field(row, "phase").ok_or(Error::Metadata)?)?;
                    if phase_name != "ApplyExtrinsic"
                        || phase_fields.values().next().and_then(ScaleValue::as_u128)
                            != Some(index as u128)
                    {
                        continue;
                    }
                    let (pallet, nested) = variant(field(row, "event").ok_or(Error::Metadata)?)?;
                    if pallet != "Midnight" {
                        continue;
                    }
                    let event = nested.values().next().ok_or(Error::Metadata)?;
                    let (name, _) = variant(event)?;
                    if matches!(name, "TxPartialSuccess" | "TxRejected") {
                        return Err(Error::Replay);
                    }
                    if !matches!(name, "TxApplied" | "ContractCall" | "ContractDeploy") {
                        continue;
                    }
                    let tx_hash = scale_bytes(field(event, "tx_hash").ok_or(Error::Metadata)?)?;
                    check(
                        hex::encode(tx_hash) == transaction.transaction_id(),
                        Error::Response,
                    )?;
                    if name == "TxApplied" {
                        applied += 1;
                    } else {
                        let address: coin_structure::contract::ContractAddress = native_decode(
                            &scale_bytes(field(event, "contract_address").ok_or(Error::Metadata)?)?,
                        )?;
                        let expected_event = match transaction.event() {
                            crate::client::ContractEvent::Deploy => "ContractDeploy",
                            crate::client::ContractEvent::Call => "ContractCall",
                        };
                        check(
                            name == expected_event
                                && hex::encode(address.0.0) == transaction.contract_address(),
                            Error::Response,
                        )?;
                        contract += 1;
                    }
                }
                check(applied == 1 && contract == 1, Error::Replay)?;
                let state_bytes = hex_bytes(&self.rpc.call(
                    "midnight_contractState",
                    json!([
                        transaction.contract_address(),
                        format!("0x{}", hashes[offset])
                    ]),
                )?)?;
                let state: onchain_runtime::state::ContractState<Db> = native_decode(&state_bytes)?;
                let mut canonical = Vec::new();
                serialize::tagged_serialize(&state, &mut canonical).map_err(|_| Error::State)?;
                check(canonical == state_bytes, Error::State)?;
                use blake2::Digest;
                let extrinsic_hash = hex::encode(
                    blake2::Blake2b::<blake2::digest::consts::U32>::digest(&expected),
                );
                let receipt = crate::client::FinalizedReceipt {
                    chain: self
                        .rpc
                        .chain_identity(&hashes[offset], &self.policy.profile)?,
                    block_hash: hashes[offset].clone(),
                    height: numbers[offset],
                    finalized_hash: final_hash.clone(),
                    finalized_height: height,
                    extrinsic_hash,
                    extrinsic_index: index as u32,
                    transaction_id: transaction.transaction_id().into(),
                    intent_id: transaction.intent_id().into(),
                    contract_address: transaction.contract_address().into(),
                    event: transaction.event(),
                    contract_state: canonical,
                };
                transaction
                    .check_receipt(&receipt)
                    .map_err(|_| Error::Response)?;
                check(found.is_none(), Error::Replay)?;
                found = Some(receipt);
            }
        }
        validate_finalized_tip(previous.as_deref(), &final_hash)?;
        Ok(found)
    }
}

fn validate_parent(previous: Option<&str>, parent: &str) -> Result<()> {
    check(previous.is_none_or(|hash| hash == parent), Error::Replay)
}
fn validate_finalized_tip(last: Option<&str>, finalized: &str) -> Result<()> {
    check(last.is_none_or(|hash| hash == finalized), Error::Replay)
}
fn cache_matches(cache: &ReplayCache, snapshot: &Snapshot) -> bool {
    cache.hash == snapshot.finalized_hash
        && cache.height == snapshot.height
        && cache.state == snapshot.state
        && cache.block.tblock == snapshot.block.tblock
        && cache.block.tblock_err == snapshot.block.tblock_err
        && cache.block.parent_block_hash == snapshot.block.parent_block_hash
        && cache.block.last_block_time == snapshot.block.last_block_time
}

// Pool refusal after an unknown broadcast does not establish absence of ledger effects.
fn pool_submission(code: Option<i64>, finalized: bool) -> crate::client::Submission {
    if code == Some(1013) || finalized {
        crate::client::Submission::Broadcast
    } else {
        crate::client::Submission::Uncertain
    }
}

impl crate::client::ChainAdapter for Node {
    async fn snapshot(&self) -> std::result::Result<Snapshot, crate::client::HostFailure> {
        self.sync().map_err(|_| crate::client::HostFailure)
    }
    async fn submit(
        &self,
        transaction: &crate::client::BoundTransaction,
    ) -> std::result::Result<crate::client::Submission, crate::client::HostFailure> {
        use crate::client::{HostFailure, Submission};
        let at = hash_text(
            &self
                .rpc
                .call("chain_getFinalizedHead", json!([]))
                .map_err(|_| HostFailure)?,
        )
        .map_err(|_| HostFailure)?;
        self.policy
            .check(
                &self
                    .rpc
                    .chain_identity(&at, &self.policy.profile)
                    .map_err(|_| HostFailure)?,
            )
            .map_err(|_| HostFailure)?;
        self.check_runtime(&at).map_err(|_| HostFailure)?;
        let metadata = self.rpc.metadata(&at).map_err(|_| HostFailure)?;
        let extrinsic = metadata
            .extrinsic(transaction.bytes())
            .map_err(|_| HostFailure)?;
        let response = match self.rpc.send(&json!({"jsonrpc":"2.0","id":1,"method":"author_submitExtrinsic","params":[format!("0x{}",hex::encode(&extrinsic))]})) { Ok(response) => response, Err(_) => return Ok(Submission::Uncertain) };
        if response["id"] != 1 || response["jsonrpc"] != "2.0" {
            return Ok(Submission::Uncertain);
        }
        if let Some(error) = response.get("error") {
            let code = error["code"].as_i64();
            let finalized = matches!(code, Some(1010..=1016))
                && self
                    .receipt(transaction)
                    .is_ok_and(|receipt| receipt.is_some());
            return Ok(pool_submission(code, finalized));
        }
        use blake2::Digest;
        let expected = hex::encode(blake2::Blake2b::<blake2::digest::consts::U32>::digest(
            &extrinsic,
        ));
        if hash_text(&response["result"]).ok().as_deref() == Some(expected.as_str()) {
            Ok(Submission::Broadcast)
        } else {
            Ok(Submission::Uncertain)
        }
    }
    async fn observe(
        &self,
        transaction: &crate::client::BoundTransaction,
    ) -> std::result::Result<crate::client::Observation, crate::client::HostFailure> {
        self.receipt(transaction)
            .map(|receipt| {
                receipt
                    .map(crate::client::Observation::Finalized)
                    .unwrap_or(crate::client::Observation::Pending)
            })
            .map_err(|_| crate::client::HostFailure)
    }
}

pub struct DevelopmentFunding<'a> {
    node: &'a Node,
    material: &'a crate::funding::DustMaterial,
    parameters: &'a crate::proof::TrustedParameters,
    policy: crate::funding::FeePolicy,
    rng: RefCell<Option<rand::rngs::StdRng>>,
}
impl<'a> DevelopmentFunding<'a> {
    pub fn new(
        node: &'a Node,
        material: &'a crate::funding::DustMaterial,
        parameters: &'a crate::proof::TrustedParameters,
        policy: crate::funding::FeePolicy,
        rng: rand::rngs::StdRng,
    ) -> Self {
        Self {
            node,
            material,
            parameters,
            policy,
            rng: RefCell::new(Some(rng)),
        }
    }
}
impl crate::client::FundingAdapter for DevelopmentFunding<'_> {
    async fn fund(
        &self,
        contract: &crate::proof::ProvedNativeIntent,
        snapshot: &Snapshot,
        policy: &NetworkPolicy,
    ) -> std::result::Result<crate::funding::UnsealedTransaction, crate::client::HostFailure> {
        use crate::client::HostFailure;
        policy.check(&snapshot.chain).map_err(|_| HostFailure)?;
        if *policy != self.node.policy {
            return Err(HostFailure);
        }
        let state = {
            let cache = self.node.cache.borrow();
            let cache = cache.as_ref().ok_or(HostFailure)?;
            if !cache_matches(cache, snapshot) {
                return Err(HostFailure);
            }
            cache.dust.clone()
        };
        let secret = self
            .node
            .dust_secret
            .borrow()
            .as_ref()
            .ok_or(HostFailure)?
            .clone();
        let rng = self.rng.borrow_mut().take().ok_or(HostFailure)?;
        let funded = crate::funding::DustFunding::new(secret, state)
            .fund(
                contract,
                &policy.network_id,
                &snapshot.state.parameters,
                self.material,
                self.parameters,
                snapshot.block.tblock,
                self.policy,
                rng,
            )
            .await
            .map_err(|_| HostFailure)?;
        Ok(funded.native().clone())
    }
}
/// The caller supplies an explicit approval function and a fresh entropy owner.
pub struct ExplicitSeal<F> {
    approve: F,
    rng: RefCell<Option<rand::rngs::StdRng>>,
}
impl<F> ExplicitSeal<F> {
    pub fn new(approve: F, rng: rand::rngs::StdRng) -> Self {
        Self {
            approve,
            rng: RefCell::new(Some(rng)),
        }
    }
}
impl<F: Fn(&crate::funding::UnsealedTransaction, &NetworkPolicy) -> bool>
    crate::client::SigningAdapter for ExplicitSeal<F>
{
    async fn approve_and_sign(
        &self,
        transaction: &crate::funding::UnsealedTransaction,
        snapshot: &Snapshot,
        policy: &NetworkPolicy,
    ) -> std::result::Result<crate::funding::SealedTransaction, crate::client::HostFailure> {
        policy
            .check(&snapshot.chain)
            .map_err(|_| crate::client::HostFailure)?;
        if !(self.approve)(transaction, policy) {
            return Err(crate::client::HostFailure);
        }
        Ok(transaction.seal(
            self.rng
                .borrow_mut()
                .take()
                .ok_or(crate::client::HostFailure)?,
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use sha2::Digest;
    #[test]
    fn pool_refusal_before_finality_keeps_submission_uncertain() {
        use crate::client::Submission;
        for code in [
            None,
            Some(-1),
            Some(1010),
            Some(1011),
            Some(1012),
            Some(1014),
            Some(1015),
            Some(1016),
        ] {
            assert_eq!(pool_submission(code, false), Submission::Uncertain);
            assert_eq!(pool_submission(code, true), Submission::Broadcast);
        }
        assert_eq!(pool_submission(Some(1013), false), Submission::Broadcast);
    }
    #[test]
    fn ancestry_and_funding_snapshot_mismatches_fail_closed() {
        assert!(validate_parent(Some("a"), "b").is_err());
        validate_parent(Some("a"), "a").unwrap();
        assert!(validate_finalized_tip(Some("branch"), "finalized").is_err());
        validate_finalized_tip(Some("finalized"), "finalized").unwrap();
        let state = LedgerState::<Db>::new("undeployed");
        let snapshot = Snapshot {
            chain: ChainIdentity {
                network_id: "undeployed".into(),
                genesis: "1".repeat(64),
                spec_version: 2001100,
                transaction_version: 4,
                profile: crate::profile::NAME.into(),
            },
            finalized_hash: "2".repeat(64),
            height: 10,
            state: state.clone(),
            block: BlockContext::default(),
        };
        let mut cache = ReplayCache {
            dust: DustLocalState::new(state.parameters.dust),
            state,
            height: 10,
            hash: "2".repeat(64),
            block: BlockContext::default(),
        };
        assert!(cache_matches(&cache, &snapshot));
        cache.hash = "3".repeat(64);
        assert!(!cache_matches(&cache, &snapshot));
        cache.hash = snapshot.finalized_hash.clone();
        cache.height += 1;
        assert!(!cache_matches(&cache, &snapshot));
        cache.height = snapshot.height;
        cache.block.tblock_err += 1;
        assert!(!cache_matches(&cache, &snapshot));
        cache.block = snapshot.block.clone();
        cache.state.network_id = "wrong".into();
        assert!(!cache_matches(&cache, &snapshot));
    }
    fn prepared_runtime(attempt: &str, address: &str) -> crate::host::Runtime {
        let context = serde_json::from_value(json!({"protocolVersion":1,"namespace":"qualification","baseRevision":"r0","attemptId":attempt,"capabilities":[{"id":"store","namespace":"qualification","keyPrefix":"claims/","operations":[crate::host::STAGE,crate::host::CAS]}],"operations":[],"providers":[],"commitCapability":"store"})).unwrap();
        let mut runtime = crate::host::Runtime::new(
            context,
            &std::collections::BTreeMap::new(),
            address.into(),
            "claim".into(),
        )
        .unwrap();
        runtime
            .stage(crate::host::Stage {
                abi_version: 1,
                operation: crate::host::STAGE.into(),
                capability: "store".into(),
                key: "claims/used".into(),
                ty: "Bool".into(),
                value: json!(true),
            })
            .unwrap();
        runtime.execution_finished(true).unwrap();
        runtime
    }
    struct LostAcknowledgement<'a>(&'a Node);
    impl crate::client::ChainAdapter for LostAcknowledgement<'_> {
        async fn snapshot(&self) -> std::result::Result<Snapshot, crate::client::HostFailure> {
            self.0.snapshot().await
        }
        async fn submit(
            &self,
            transaction: &crate::client::BoundTransaction,
        ) -> std::result::Result<crate::client::Submission, crate::client::HostFailure> {
            assert_eq!(
                self.0.submit(transaction).await?,
                crate::client::Submission::Broadcast
            );
            Ok(crate::client::Submission::Uncertain)
        }
        async fn observe(
            &self,
            transaction: &crate::client::BoundTransaction,
        ) -> std::result::Result<crate::client::Observation, crate::client::HostFailure> {
            self.0.observe(transaction).await
        }
    }
    #[test]
    #[ignore = "deploys and claims on the explicitly authorized isolated local development chain"]
    fn real_rust_only_funded_deploy_and_claim() {
        use crate::{
            artifacts,
            client::{
                BoundTransaction, ChainAdapter, ContractEvent, Error as ClientError, Submission,
                SubmissionAttempt,
            },
            proof::{LocalProver, PreparedProof},
        };
        use futures::{executor::block_on, future::pending};
        use rand::{SeedableRng, rngs::OsRng};
        block_on(async {
            let policy = NetworkPolicy {
                network_id: "undeployed".into(),
                genesis: "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d".into(),
                spec_version: 2001100,
                transaction_version: 4,
                profile: crate::profile::NAME.into(),
                max_dust: 10u128.pow(22),
            };
            let mut node = Node::connect(
                "http://127.0.0.1:19944",
                policy.clone(),
                Duration::from_secs(30),
                64 * 1024 * 1024,
                10_000,
            )
            .unwrap();
            let mut seed = [0u8; 32];
            seed[31] = 1;
            node.attach_dust_seed(&seed).unwrap();
            let snapshot = node.sync().unwrap();
            node.metadata.fingerprint[0] ^= 1;
            assert_eq!(node.sync().err(), Some(Error::Metadata));
            node.metadata.fingerprint[0] ^= 1;
            let code = node.runtime_code.clone();
            node.runtime_code = "0".repeat(64);
            assert_eq!(node.sync().err(), Some(Error::Metadata));
            node.runtime_code = code;
            let cache = ProofCache::new(
                "/private/tmp/nightlean-proof-params".into(),
                reqwest::Url::parse("https://srs.midnight.network/").unwrap(),
            )
            .unwrap();
            let material = cache.dust().await.unwrap();
            let dust_srs = cache.parameters(material.k()).await.unwrap();
            let bundle = artifacts::verify(
                std::path::Path::new(&std::env::var("NIGHTLEAN_TEST_BUNDLE").unwrap()),
                Some(&std::env::var("NIGHTLEAN_TEST_MANIFEST_SHA256").unwrap()),
            )
            .unwrap();
            let config = zeroize::Zeroizing::new(
                std::fs::read(std::env::var("NIGHTLEAN_TEST_PRIVATE_CONFIG").unwrap()).unwrap(),
            );
            let prepared = PreparedProof::from_config(
                &bundle,
                &config,
                snapshot.block.tblock.to_secs() + 1800,
                &mut OsRng,
            )
            .unwrap();
            let private = crate::parse_private_config(&config).unwrap();
            assert_eq!(private.negative_cases.len(), 5);
            let mut negative_claims = Vec::new();
            for case in &private.negative_cases {
                let mut modified: Json = serde_json::from_slice(&config).unwrap();
                modified["inputs"] = serde_json::to_value(&case.inputs).unwrap();
                let encoded = zeroize::Zeroizing::new(serde_json::to_vec(&modified).unwrap());
                assert!(
                    PreparedProof::from_config(
                        &bundle,
                        &encoded,
                        snapshot.block.tblock.to_secs() + 1800,
                        &mut OsRng
                    )
                    .is_err()
                );
                negative_claims.push(case.name.clone());
            }
            let mut wrong_genesis = policy.clone();
            wrong_genesis.genesis = "0".repeat(64);
            assert_eq!(
                Node::connect(
                    "http://127.0.0.1:19944",
                    wrong_genesis,
                    Duration::from_secs(30),
                    64 * 1024 * 1024,
                    10_000
                )
                .err(),
                Some(Error::Network)
            );
            let mut wrong_profile = policy.clone();
            wrong_profile.profile = "unsupported-profile".into();
            assert_eq!(
                Node::connect(
                    "http://127.0.0.1:19944",
                    wrong_profile,
                    Duration::from_secs(30),
                    64 * 1024 * 1024,
                    10_000
                )
                .err(),
                Some(Error::Policy)
            );
            let call_srs = cache.parameters(prepared.k()).await.unwrap();
            let call = prepared
                .prove(
                    &LocalProver::new(rand::rngs::StdRng::from_entropy()),
                    &call_srs,
                    1_048_576,
                    pending(),
                )
                .await
                .unwrap();
            let provider = builtin_zkir::LocalProvingProvider {
                rng: rand::rngs::StdRng::from_entropy(),
                resolver: &material,
                params: &dust_srs,
            };
            let (_, deploy) = prepared
                .deployment_intent()
                .unwrap()
                .prove(
                    crate::funding::CONTRACT_SEGMENT,
                    provider,
                    &snapshot.state.parameters.cost_model.runtime_cost_model,
                )
                .await
                .unwrap();
            let journal_dir = std::path::PathBuf::from(format!(
                "/private/tmp/nightlean-native-journal-{}-{}",
                std::process::id(),
                snapshot.height
            ));
            let mut evidence = Vec::new();
            let mut accepted = Vec::new();
            for (kind, intent) in [
                (ContractEvent::Deploy, &deploy),
                (ContractEvent::Call, call.native()),
            ] {
                let funding = DevelopmentFunding::new(
                    &node,
                    &material,
                    &dust_srs,
                    crate::funding::FeePolicy {
                        max_dust: policy.max_dust,
                        margin_blocks: 3,
                        max_spends: 8,
                    },
                    rand::rngs::StdRng::from_entropy(),
                );
                let mut mismatched = node.sync().unwrap();
                mismatched.height += 1;
                assert!(
                    crate::client::FundingAdapter::fund(&funding, intent, &mismatched, &policy)
                        .await
                        .is_err()
                );
                assert!(funding.rng.borrow().is_some());
                let signing = ExplicitSeal::new(
                    |_: &crate::funding::UnsealedTransaction, p: &NetworkPolicy| {
                        p.genesis
                            == "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d"
                            && p.max_dust <= 10u128.pow(22)
                    },
                    rand::rngs::StdRng::from_entropy(),
                );
                let bound =
                    BoundTransaction::prepare(intent, policy.clone(), &node, &funding, &signing)
                        .await
                        .unwrap();
                assert_eq!(bound.event(), kind);
                if kind == ContractEvent::Call {
                    use ledger::structure::{ContractAction, ProofVersioned, Transaction};
                    use storage::arena::Sp;
                    let current = node.sync().unwrap();
                    for mutation in ["proof", "publicCommitment", "network"] {
                        let mut invalid: crate::funding::SealedTransaction =
                            native_decode(bound.bytes()).unwrap();
                        let Transaction::Standard(stx) = &mut invalid else {
                            panic!("standard transaction")
                        };
                        if mutation == "network" {
                            stx.network_id = "wrong-network".into();
                        } else {
                            let mut intent =
                                (*stx.intents.get(&crate::funding::CONTRACT_SEGMENT).unwrap())
                                    .clone();
                            let mut actions: Vec<_> =
                                intent.actions.iter_deref().cloned().collect();
                            let ContractAction::Call(call) = &mut actions[0] else {
                                panic!("claim call")
                            };
                            let mut changed = (**call).clone();
                            if mutation == "proof" {
                                let ProofVersioned::V3(proof) = &mut changed.proof else {
                                    panic!("v3 proof")
                                };
                                proof.0[0] ^= 1;
                            } else {
                                changed.communication_commitment.0 +=
                                    transient_crypto::curve::Fr::from(1u64).0;
                            }
                            *call = Sp::new(changed);
                            intent.actions = actions.into();
                            stx.intents =
                                stx.intents.insert(crate::funding::CONTRACT_SEGMENT, intent);
                        }
                        assert!(
                            invalid
                                .well_formed(
                                    &current.state,
                                    WellFormedStrictness::default(),
                                    current.block.tblock
                                )
                                .is_err(),
                            "{mutation}"
                        );
                        let mut bytes = Vec::new();
                        serialize::tagged_serialize(&invalid, &mut bytes).unwrap();
                        let extrinsic = node.metadata.extrinsic(&bytes).unwrap();
                        let response = node.rpc.send(&json!({"jsonrpc":"2.0","id":1,"method":"author_submitExtrinsic","params":[format!("0x{}",hex::encode(extrinsic))]})).unwrap();
                        assert!(
                            response.get("error").is_some(),
                            "invalid {mutation} refused before pool acceptance"
                        );
                    }
                }
                let attempt_id = hex::encode(sha2::Sha256::digest(format!(
                    "{}:{}",
                    bound.transaction_id(),
                    snapshot.height
                )));
                let address = bound.contract_address().to_owned();
                let expected_bytes = bound.bytes().to_vec();
                let store =
                    journal::DirectoryJournal::new(&journal_dir, Duration::from_secs(2)).unwrap();
                let mut runtime = prepared_runtime(&attempt_id, &address);
                let mut attempt = SubmissionAttempt::new(bound, &attempt_id, &mut runtime).unwrap();
                assert_eq!(
                    attempt
                        .submit_once(&mut runtime, &LostAcknowledgement(&node), &store)
                        .await
                        .unwrap(),
                    Submission::Uncertain
                );
                assert_eq!(
                    attempt.cancel(&mut runtime, &store).await,
                    Err(ClientError::CancellationAfterBroadcast)
                );
                assert_eq!(
                    attempt.deadline(&mut runtime, &store).await,
                    Err(ClientError::Deadline)
                );
                drop((attempt, runtime, store));
                let store =
                    journal::DirectoryJournal::new(&journal_dir, Duration::from_secs(2)).unwrap();
                let mut attempt = SubmissionAttempt::recover(&store, &attempt_id)
                    .await
                    .unwrap();
                assert_eq!(attempt.transaction().bytes(), expected_bytes);
                let mut runtime = prepared_runtime(&attempt_id, &address);
                attempt.restore_runtime(&mut runtime).unwrap();
                // Retransmit only the durable sealed transaction after an unknown outcome.
                assert_eq!(
                    attempt
                        .submit_once(&mut runtime, &node, &store)
                        .await
                        .unwrap(),
                    Submission::Broadcast
                );
                let deadline = std::time::Instant::now() + Duration::from_secs(90);
                loop {
                    if let Some(receipt) = attempt
                        .observe_once(&mut runtime, &node, &store)
                        .await
                        .unwrap()
                    {
                        let transaction = attempt.transaction();
                        for mutation in [
                            "genesis",
                            "profile",
                            "transaction",
                            "intent",
                            "address",
                            "state",
                            "finality",
                        ] {
                            let mut wrong = receipt.clone();
                            match mutation {
                                "genesis" => wrong.chain.genesis = "0".repeat(64),
                                "profile" => wrong.chain.profile = "wrong-profile".into(),
                                "transaction" => wrong.transaction_id = "0".repeat(64),
                                "intent" => wrong.intent_id = "0".repeat(64),
                                "address" => wrong.contract_address = "0".repeat(64),
                                "state" => wrong.contract_state.push(0),
                                "finality" => wrong.finalized_height = wrong.height - 1,
                                _ => unreachable!(),
                            }
                            assert!(transaction.check_receipt(&wrong).is_err(), "{mutation}");
                        }
                        let state_digest =
                            hex::encode(sha2::Sha256::digest(&receipt.contract_state));
                        evidence.push(json!({"event":format!("{kind:?}"),"height":receipt.height,"blockHash":receipt.block_hash,"transactionId":transaction.transaction_id(),"intentId":transaction.intent_id(),"contractAddress":transaction.contract_address(),"contractStateBytes":receipt.contract_state.len(),"contractStateSha256":state_digest,"extrinsicHash":receipt.extrinsic_hash,"extrinsicIndex":receipt.extrinsic_index}));
                        eprintln!(
                            "native Rust {:?} finalized at height {}, transaction {}, contract {}, exact state SHA256 {}",
                            kind,
                            receipt.height,
                            transaction.transaction_id(),
                            transaction.contract_address(),
                            state_digest
                        );
                        break;
                    }
                    assert!(std::time::Instant::now() < deadline);
                    std::thread::sleep(Duration::from_millis(500));
                }
                accepted.push((attempt, runtime));
            }
            let store =
                journal::DirectoryJournal::new(&journal_dir, Duration::from_secs(2)).unwrap();
            let (mut deployment, mut runtime) = accepted.remove(0);
            let deployment_id = deployment.record().identity().attempt_id.clone();
            let receipt = deployment
                .commit_private(&mut runtime, &store, 7)
                .await
                .unwrap();
            assert!(receipt.committed);
            assert_eq!(store.revision("qualification").unwrap(), "r1");
            assert_eq!(
                store
                    .private_value("qualification", "claims/used")
                    .unwrap()
                    .unwrap()["value"],
                true
            );
            assert!(
                deployment
                    .commit_private(&mut runtime, &store, 7)
                    .await
                    .unwrap()
                    .committed
            );
            let (mut claim, mut runtime) = accepted.remove(0);
            let claim_receipt = claim.commit_private(&mut runtime, &store, 8).await.unwrap();
            assert!(!claim_receipt.committed);
            assert_eq!(claim_receipt.revision, "r1");
            assert_eq!(store.revision("qualification").unwrap(), "r1");
            drop(deployment);
            let mut recovered = SubmissionAttempt::recover(&store, &deployment_id)
                .await
                .unwrap();
            let mut runtime =
                prepared_runtime(&deployment_id, recovered.transaction().contract_address());
            recovered.restore_runtime(&mut runtime).unwrap();
            assert_eq!(
                recovered
                    .commit_private(&mut runtime, &store, 9)
                    .await
                    .err(),
                Some(ClientError::Receipt)
            );
            recovered
                .observe_once(&mut runtime, &node, &store)
                .await
                .unwrap()
                .unwrap();
            assert!(
                recovered
                    .commit_private(&mut runtime, &store, 9)
                    .await
                    .unwrap()
                    .committed
            );
            assert_eq!(store.revision("qualification").unwrap(), "r1");
            // The exact accepted transaction stays an idempotent client retry. A raw
            // duplicate submission is refused by the native pool and never rebuilt.
            assert_eq!(
                node.submit(&claim.transaction()).await.unwrap(),
                Submission::Broadcast
            );
            let replay = node.rpc.send(&json!({"jsonrpc":"2.0","id":1,"method":"author_submitExtrinsic","params":[format!("0x{}",hex::encode(node.metadata.extrinsic(claim.transaction().bytes()).unwrap()))]})).unwrap();
            assert!(replay.get("error").is_some());
            let state: onchain_runtime::state::ContractState<Db> =
                native_decode(claim.transaction().expected_state()).unwrap();
            let plan: crate::Plan =
                serde_json::from_slice(bundle.file(artifacts::Role::Plan).unwrap()).unwrap();
            let address = coin_structure::contract::ContractAddress(HashOutput(
                hex::decode(claim.transaction().contract_address())
                    .unwrap()
                    .try_into()
                    .unwrap(),
            ));
            assert!(
                crate::prepare(
                    &plan,
                    &private.inputs,
                    &state.data,
                    &node.sync().unwrap().state.parameters,
                    address
                )
                .is_err()
            );
            if let Ok(path) = std::env::var("NIGHTLEAN_TEST_EVIDENCE") {
                let final_snapshot = node.sync().unwrap();
                let mut final_state = Vec::new();
                serialize::tagged_serialize(&final_snapshot.state, &mut final_state).unwrap();
                let value = json!({"runtimeCodeHash":node.runtime_code,"metadataVersion":16,"metadataSha256":hex::encode(&node.metadata.fingerprint),"contractParametersSha256":call_srs.sha256(),"dustParametersSha256":dust_srs.sha256(),"finalReplayHeight":final_snapshot.height,"finalReplayBlockHash":final_snapshot.finalized_hash,"nativeLedgerStateTaggedSha256":hex::encode(sha2::Sha256::digest(&final_state)),"nativeStoredLedgerRootMatchedRuntime":true,"schemaVersion":1,"scope":"native deploy and claim, lost acknowledgement, durable restart, byte-identical retry, postbroadcast cancellation/deadline, exact finalized state, committed private CAS and accepted-chain private CAS conflict","profile":crate::profile::NAME,"manifestSha256":std::env::var("NIGHTLEAN_TEST_MANIFEST_SHA256").unwrap(),"genesis":policy.genesis,"specVersion":policy.spec_version,"transactionVersion":policy.transaction_version,"journalDirectory":journal_dir,"negativeClaims":negative_claims,"invalidNativeProofRefused":true,"alteredPublicCommitmentRefused":true,"wrongNetworkRefused":true,"wrongGenesisRefused":true,"wrongProfileRefused":true,"rawReplayRefused":true,"claimedStateReplayRefused":true,"wrongReceiptFieldsRefused":true,"metadataMismatchRefused":true,"runtimeCodeMismatchRefused":true,"fundingCacheMismatchRefusedBeforeEntropyUse":true,"records":evidence});
                std::fs::write(path, serde_json::to_vec_pretty(&value).unwrap()).unwrap();
            }
        });
    }
}
