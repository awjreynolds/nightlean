//! Explicit host capabilities and private journals. No ambient I/O or durable storage.
use crate::{
    ScalarType, input_value,
    lifecycle::{Effect, Event, Lifecycle, Phase},
};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::{BTreeMap, BTreeSet};
use zeroize::Zeroize;

pub const PROTOCOL_VERSION: u32 = 1;
pub const READ: &str = "private_state.read.v1";
pub const STAGE: &str = "private_state.stage.v1";
pub const CAS: &str = "private_state.compare_exchange.v1";
pub const CAS_SCHEMA: &str = "PrivateStateCasResult/v1";
pub const MAX_PRIVATE_BYTES: usize = 65_536;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Error {
    Descriptor,
    Denied,
    State,
    Response,
    Limit,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Descriptor => "invalid host descriptor",
            Self::Denied => "host capability denied",
            Self::State => "invalid host lifecycle state",
            Self::Response => "invalid host response",
            Self::Limit => "host limit exceeded",
        })
    }
}
impl std::error::Error for Error {}
pub type Result<T> = std::result::Result<T, Error>;
fn require(value: bool, error: Error) -> Result<()> {
    if value { Ok(()) } else { Err(error) }
}
fn wipe(value: &mut Json) {
    match value {
        Json::String(v) => v.zeroize(),
        Json::Array(v) => v.iter_mut().for_each(wipe),
        Json::Object(v) => v.values_mut().for_each(wipe),
        _ => {}
    }
}
fn identifier(value: &str) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"_-.:".contains(&b))
}
fn operation(value: &str) -> bool {
    identifier(value) && value.ends_with(".v1")
}
fn key(value: &str, prefix: bool) -> bool {
    !value.is_empty()
        && value.len() <= 128
        && value
            .bytes()
            .all(|b| b.is_ascii_alphanumeric() || b"_-/.:".contains(&b))
        && !value.starts_with('/')
        && (prefix || !value.ends_with('/'))
        && value
            .strip_suffix('/')
            .unwrap_or(value)
            .split('/')
            .all(|s| !s.is_empty() && s != "." && s != "..")
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Context {
    pub protocol_version: u32,
    pub namespace: String,
    pub base_revision: String,
    pub attempt_id: String,
    pub capabilities: Vec<Capability>,
    pub operations: Vec<Operation>,
    pub providers: Vec<Provider>,
    pub commit_capability: String,
    #[serde(default)]
    pub limits: Limits,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Capability {
    pub id: String,
    pub namespace: String,
    pub key_prefix: String,
    pub operations: Vec<String>,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Operation {
    pub operation: String,
    pub argument_schema: BTreeMap<String, String>,
    pub result_schema: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Provider {
    pub input: String,
    pub operation: String,
    pub capability: String,
    pub arguments: BTreeMap<String, Json>,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Limits {
    pub requests: usize,
    pub writes: usize,
    pub private_bytes: usize,
}
impl Default for Limits {
    fn default() -> Self {
        Self {
            requests: 64,
            writes: 64,
            private_bytes: MAX_PRIVATE_BYTES,
        }
    }
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Stage {
    pub abi_version: u32,
    pub operation: String,
    pub capability: String,
    pub key: String,
    #[serde(rename = "type")]
    pub ty: String,
    pub value: Json,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
pub struct Notice {
    pub abi_version: u32,
    pub event: String,
    pub attempt_id: String,
    pub transaction_id: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CasResponse {
    attempt_id: String,
    transaction_id: String,
    journal_digest: String,
    outcome: String,
    base_revision: String,
    revision: String,
}
struct Write {
    ty: String,
    value: Json,
}
impl Drop for Write {
    fn drop(&mut self) {
        wipe(&mut self.value);
    }
}
enum Pending {
    Provider { id: u64, input: String },
    Cas { id: u64 },
}
pub struct Runtime {
    context: Context,
    lifecycle: Lifecycle,
    target: String,
    entrypoint: String,
    writes: BTreeMap<String, Write>,
    pending: Option<Pending>,
    requests: usize,
}
impl Runtime {
    pub fn new(
        context: Context,
        private_inputs: &BTreeMap<String, String>,
        target: String,
        entrypoint: String,
    ) -> Result<Self> {
        require(
            context.protocol_version == PROTOCOL_VERSION && identifier(&context.namespace),
            Error::Descriptor,
        )?;
        require(
            context.capabilities.len() <= 32
                && context.operations.len() <= 32
                && context.providers.len() <= 32,
            Error::Limit,
        )?;
        require(
            context.limits.requests > private_inputs.len()
                && context.limits.requests <= 257
                && context.limits.writes > 0
                && context.limits.writes <= 64
                && context.limits.private_bytes >= 1024
                && context.limits.private_bytes <= MAX_PRIVATE_BYTES,
            Error::Limit,
        )?;
        let lifecycle = Lifecycle::new(context.attempt_id.clone(), context.base_revision.clone())
            .map_err(|_| Error::Descriptor)?;
        let mut names = BTreeSet::new();
        for capability in &context.capabilities {
            require(
                identifier(&capability.id)
                    && names.insert(capability.id.clone())
                    && capability.namespace == context.namespace
                    && key(&capability.key_prefix, true)
                    && !capability.operations.is_empty()
                    && capability.operations.len() <= 32,
                Error::Descriptor,
            )?;
            let mut ops = BTreeSet::new();
            for name in &capability.operations {
                require(operation(name) && ops.insert(name), Error::Descriptor)?;
            }
        }
        names.clear();
        for descriptor in &context.operations {
            require(
                operation(&descriptor.operation)
                    && !matches!(descriptor.operation.as_str(), STAGE | CAS)
                    && names.insert(descriptor.operation.clone())
                    && descriptor.argument_schema.len() <= 8
                    && ScalarType::parse(&descriptor.result_schema).is_ok(),
                Error::Descriptor,
            )?;
            for (name, ty) in &descriptor.argument_schema {
                require(
                    identifier(name) && (ty == "Key" || ScalarType::parse(ty).is_ok()),
                    Error::Descriptor,
                )?;
            }
            if descriptor.operation == READ {
                require(
                    descriptor.argument_schema == BTreeMap::from([("key".into(), "Key".into())]),
                    Error::Descriptor,
                )?;
            }
        }
        names.clear();
        let runtime = Self {
            context,
            lifecycle,
            target,
            entrypoint,
            writes: BTreeMap::new(),
            pending: None,
            requests: 0,
        };
        runtime.grant(&runtime.context.commit_capability, CAS, None)?;
        for provider in &runtime.context.providers {
            require(
                names.insert(provider.input.clone())
                    && private_inputs.contains_key(&provider.input),
                Error::Descriptor,
            )?;
            let descriptor = runtime.descriptor(&provider.operation)?;
            require(
                private_inputs[&provider.input] == descriptor.result_schema
                    && provider.arguments.len() == descriptor.argument_schema.len(),
                Error::Descriptor,
            )?;
            runtime.grant(&provider.capability, &provider.operation, None)?;
            for (name, ty) in &descriptor.argument_schema {
                let value = provider.arguments.get(name).ok_or(Error::Descriptor)?;
                if ty == "Key" {
                    let value = value.as_str().ok_or(Error::Descriptor)?;
                    require(key(value, false), Error::Descriptor)?;
                    runtime.grant(&provider.capability, &provider.operation, Some(value))?;
                } else {
                    input_value(ty, value).map_err(|_| Error::Descriptor)?;
                }
            }
        }
        // Bound the retained descriptor/argument envelope as well as later journal exports.
        require(
            runtime.private_size()? <= runtime.context.limits.private_bytes,
            Error::Limit,
        )?;
        Ok(runtime)
    }
    fn descriptor(&self, name: &str) -> Result<&Operation> {
        self.context
            .operations
            .iter()
            .find(|d| d.operation == name)
            .ok_or(Error::Descriptor)
    }
    fn provider(&self, input: &str) -> Option<&Provider> {
        self.context.providers.iter().find(|p| p.input == input)
    }
    fn grant(&self, id: &str, operation: &str, key: Option<&str>) -> Result<()> {
        let capability = self
            .context
            .capabilities
            .iter()
            .find(|c| c.id == id)
            .ok_or(Error::Denied)?;
        require(
            capability.namespace == self.context.namespace
                && capability.operations.iter().any(|op| op == operation),
            Error::Denied,
        )?;
        if let Some(key) = key {
            require(
                if capability.key_prefix.ends_with('/') {
                    key.starts_with(&capability.key_prefix)
                } else {
                    key == capability.key_prefix
                },
                Error::Denied,
            )?;
        }
        Ok(())
    }
    fn private_size(&self) -> Result<usize> {
        let writes: BTreeMap<_, _> = self
            .writes
            .iter()
            .map(|(k, w)| (k, json!({"type":w.ty,"value":w.value})))
            .collect();
        let args: Vec<_> = self
            .context
            .providers
            .iter()
            .map(|p| &p.arguments)
            .collect();
        let transaction = self
            .lifecycle
            .transaction_id()
            .unwrap_or("0000000000000000000000000000000000000000000000000000000000000000");
        serde_json::to_vec(&json!({"journal":{"protocolVersion":1,"attemptId":self.lifecycle.attempt_id(),"transactionId":transaction,"namespace":self.context.namespace,"baseRevision":self.lifecycle.base_revision(),"contractAddress":self.target,"entrypoint":self.entrypoint,"writes":writes},"arguments":args}))
            .map(|mut v| {let length=v.len();v.zeroize();length+128})
            .map_err(|_| Error::Descriptor)
    }
    fn count_request(&mut self) -> Result<()> {
        require(self.requests < self.context.limits.requests, Error::Limit)?;
        self.requests += 1;
        Ok(())
    }
    pub fn begin_input(&mut self, input: &str, id: u64) -> Result<Option<Json>> {
        require(
            self.lifecycle.phase() == Phase::Open && self.pending.is_none(),
            Error::State,
        )?;
        self.count_request()?;
        if self.provider(input).is_some() {
            self.pending = Some(Pending::Provider {
                id,
                input: input.to_owned(),
            });
            self.input_metadata()
        } else {
            Ok(None)
        }
    }
    pub fn input_metadata(&self) -> Result<Option<Json>> {
        let Some(Pending::Provider { id, input }) = &self.pending else {
            return Ok(None);
        };
        let provider = self.provider(input).ok_or(Error::State)?;
        let descriptor = self.descriptor(&provider.operation)?;
        Ok(Some(
            json!({"id":id,"operation":provider.operation,"capability":provider.capability,"schema":descriptor.result_schema,"name":input,"type":descriptor.result_schema,"visibility":"private","hasPrivateArguments":true,"protocolVersion":1}),
        ))
    }
    pub fn finish_input(
        &mut self,
        input: &str,
        id: u64,
        operation: Option<&str>,
        capability: Option<&str>,
        schema: Option<&str>,
        value: &Json,
    ) -> Result<()> {
        if self.provider(input).is_none() {
            return require(
                operation.is_none() && capability.is_none() && schema.is_none(),
                Error::Response,
            );
        }
        let Some(Pending::Provider {
            id: expected,
            input: pending,
        }) = &self.pending
        else {
            return Err(Error::State);
        };
        require(*expected == id && pending == input, Error::Response)?;
        let provider = self.provider(input).ok_or(Error::State)?;
        let descriptor = self.descriptor(&provider.operation)?;
        require(
            operation == Some(provider.operation.as_str())
                && capability == Some(provider.capability.as_str())
                && schema == Some(descriptor.result_schema.as_str()),
            Error::Response,
        )?;
        input_value(&descriptor.result_schema, value).map_err(|_| Error::Response)?;
        self.pending = None;
        Ok(())
    }
    pub fn stage(&mut self, stage: Stage) -> Result<()> {
        require(self.lifecycle.phase() == Phase::Open, Error::State)?;
        require(
            stage.abi_version == 1 && stage.operation == STAGE && key(&stage.key, false),
            Error::Descriptor,
        )?;
        self.grant(&stage.capability, STAGE, Some(&stage.key))?;
        self.grant(&self.context.commit_capability, CAS, Some(&stage.key))?;
        input_value(&stage.ty, &stage.value).map_err(|_| Error::Response)?;
        require(
            self.writes.contains_key(&stage.key) || self.writes.len() < self.context.limits.writes,
            Error::Limit,
        )?;
        let old = self.writes.insert(
            stage.key.clone(),
            Write {
                ty: stage.ty,
                value: stage.value,
            },
        );
        if self.private_size()? > self.context.limits.private_bytes {
            self.writes.remove(&stage.key);
            if let Some(old) = old {
                self.writes.insert(stage.key, old);
            }
            return Err(Error::Limit);
        }
        Ok(())
    }
    fn effect(&mut self, effect: Effect) {
        if effect == Effect::DropJournal {
            self.clear_writes();
            self.pending = None;
        }
    }
    fn clear_writes(&mut self) {
        for (mut key, write) in std::mem::take(&mut self.writes) {
            key.zeroize();
            drop(write);
        }
    }
    pub fn execution_finished(&mut self, success: bool) -> Result<()> {
        let effect = self
            .lifecycle
            .apply(if success {
                Event::ExecutionSucceeded
            } else {
                Event::ExecutionFailed
            })
            .map_err(|_| Error::State)?;
        self.effect(effect);
        require(self.lifecycle.invariant(), Error::State)
    }
    pub fn cancel(&mut self) -> Result<()> {
        let effect = self
            .lifecycle
            .apply(Event::Cancel)
            .map_err(|_| Error::State)?;
        self.effect(effect);
        Ok(())
    }
    pub fn notify(&mut self, notice: Notice) -> Result<bool> {
        require(notice.abi_version == 1, Error::Response)?;
        let event = match notice.event.as_str() {
            "bind" => {
                require(
                    notice.attempt_id == self.lifecycle.attempt_id(),
                    Error::Response,
                )?;
                Event::Bind {
                    transaction_id: notice.transaction_id,
                }
            }
            "persisted" => Event::Persisted {
                transaction_id: notice.transaction_id,
                attempt_id: notice.attempt_id,
            },
            "submitted" => Event::Submitted {
                transaction_id: notice.transaction_id,
                attempt_id: notice.attempt_id,
            },
            "accepted" => Event::Accepted {
                transaction_id: notice.transaction_id,
                attempt_id: notice.attempt_id,
            },
            "rejected" => Event::Rejected {
                transaction_id: notice.transaction_id,
                attempt_id: notice.attempt_id,
            },
            "uncertain" => Event::Uncertain {
                transaction_id: notice.transaction_id,
                attempt_id: notice.attempt_id,
            },
            _ => return Err(Error::Response),
        };
        let effect = self.lifecycle.apply(event).map_err(|_| Error::State)?;
        let request = effect == Effect::RequestCas;
        self.effect(effect);
        require(self.lifecycle.invariant(), Error::State)?;
        Ok(request)
    }
    pub fn begin_cas(&mut self, id: u64) -> Result<()> {
        if matches!(self.pending, Some(Pending::Cas { .. })) {
            return Ok(());
        }
        require(
            self.lifecycle.phase() == Phase::AwaitingCas && self.pending.is_none(),
            Error::State,
        )?;
        self.count_request()?;
        self.pending = Some(Pending::Cas { id });
        Ok(())
    }
    pub fn cas_metadata(&self) -> Option<Json> {
        let Some(Pending::Cas { id }) = self.pending else {
            return None;
        };
        Some(
            json!({"id":id,"operation":CAS,"capability":self.context.commit_capability,"schema":CAS_SCHEMA,"hasPrivateArguments":true,"protocolVersion":1}),
        )
    }
    pub fn finish_cas(
        &mut self,
        id: u64,
        operation: Option<&str>,
        capability: Option<&str>,
        schema: Option<&str>,
        value: Json,
    ) -> Result<()> {
        let Some(Pending::Cas { id: expected }) = self.pending else {
            return Err(Error::State);
        };
        require(
            id == expected
                && operation == Some(CAS)
                && capability == Some(self.context.commit_capability.as_str())
                && schema == Some(CAS_SCHEMA),
            Error::Response,
        )?;
        let value: CasResponse = serde_json::from_value(value).map_err(|_| Error::Response)?;
        require(
            self.private_journal()?["journalDigest"].as_str()
                == Some(value.journal_digest.as_str()),
            Error::Response,
        )?;
        let transaction_id = value.transaction_id;
        let attempt_id = value.attempt_id;
        let event = match value.outcome.as_str() {
            "committed" => Event::CasCommitted {
                transaction_id,
                attempt_id,
                base_revision: value.base_revision,
                revision: value.revision,
            },
            "conflict" => Event::CasConflict {
                transaction_id,
                attempt_id,
                base_revision: value.base_revision,
                revision: value.revision,
            },
            _ => return Err(Error::Response),
        };
        let effect = self.lifecycle.apply(event).map_err(|_| Error::Response)?;
        self.pending = None;
        self.effect(effect);
        require(self.lifecycle.invariant(), Error::State)
    }
    fn bounded(&self, value: Json) -> Result<Json> {
        require(
            serde_json::to_vec(&value)
                .map_err(|_| Error::Descriptor)?
                .len()
                <= self.context.limits.private_bytes,
            Error::Limit,
        )?;
        Ok(value)
    }
    pub fn private_arguments(&self) -> Result<Json> {
        match &self.pending {
            Some(Pending::Provider { id, input }) => {
                let provider = self.provider(input).ok_or(Error::State)?;
                self.bounded(json!({"protocolVersion":1,"requestId":id,"namespace":self.context.namespace,"arguments":provider.arguments}))
            }
            Some(Pending::Cas { id }) => self.bounded(
                json!({"protocolVersion":1,"requestId":id,"journal":self.private_journal()?}),
            ),
            None => Err(Error::State),
        }
    }
    pub fn private_journal(&self) -> Result<Json> {
        require(
            matches!(
                self.lifecycle.phase(),
                Phase::Prepared | Phase::Submitted | Phase::Uncertain | Phase::AwaitingCas
            ),
            Error::State,
        )?;
        let transaction = self.lifecycle.transaction_id().ok_or(Error::State)?;
        let writes: BTreeMap<_, _> = self
            .writes
            .iter()
            .map(|(key, write)| (key, json!({"type":write.ty,"value":write.value})))
            .collect();
        let mut journal = json!({"protocolVersion":1,"attemptId":self.lifecycle.attempt_id(),"transactionId":transaction,"namespace":self.context.namespace,"baseRevision":self.lifecycle.base_revision(),"contractAddress":self.target,"entrypoint":self.entrypoint,"writes":writes});
        // Root and write maps use lexical keys. Scalar write values have one canonical encoding.
        let canonical: BTreeMap<String, Json> =
            serde_json::from_value(journal.clone()).map_err(|_| Error::Descriptor)?;
        let mut bytes = serde_json::to_vec(&canonical).map_err(|_| Error::Descriptor)?;
        let mut hasher = Sha256::new();
        hasher.update(b"nightlean.private-state-journal.v1\0");
        hasher.update(&bytes);
        journal["journalDigest"] = json!(hex::encode(hasher.finalize()));
        bytes.zeroize();
        self.bounded(journal)
    }
    pub fn public_status(&self) -> Json {
        let phase = match self.lifecycle.phase() {
            Phase::Open => "open",
            Phase::Prepared => "prepared",
            Phase::Submitted => "submitted",
            Phase::Uncertain => "uncertain",
            Phase::AwaitingCas => "awaiting_cas",
            Phase::Committed => "committed",
            Phase::Rejected => "rejected",
            Phase::Cancelled => "cancelled",
            Phase::Failed => "failed",
            Phase::Conflicted => "conflicted",
        };
        json!({"abiVersion":1,"status":"private_state","phase":phase,"acceptedHostEvidence":self.lifecycle.accepted_host_evidence(),"hostCasAcknowledged":self.lifecycle.phase()==Phase::Committed})
    }
    pub fn invariant(&self) -> bool {
        self.lifecycle.invariant()
    }
}
impl Drop for Runtime {
    fn drop(&mut self) {
        self.clear_writes();
        for provider in &mut self.context.providers {
            provider.arguments.values_mut().for_each(wipe);
        }
    }
}
