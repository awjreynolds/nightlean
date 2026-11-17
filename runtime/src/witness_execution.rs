//! Owned Rust API for executing source witnesses and preparing their native client call.
//!
//! A `WitnessExecution` owns one authenticated source invocation and its frozen deployment
//! target. `prepare_proof` keeps that invocation available until every proof-side check passes,
//! then moves its private Runtime into `WitnessProof`. The Runtime never leaves an opaque
//! proof/client owner as a detached value.

use crate::{
    artifacts::{Role, VerifiedBundle},
    client,
    control::{self, TypedResponse},
    funding::{SealedTransaction, UnsealedTransaction},
    host,
    native_client::{self, Command, Contract, Descriptor, Driver, ServiceReply},
    proof::{
        self, PreparedProof, ProofService, ProvedIntent, ProvedNativeIntent, TrustedParameters,
    },
};
use futures::Future;
use rand::{CryptoRng, Rng};
use serde_json::Value as Json;
use std::{
    collections::BTreeMap,
    fmt,
    ops::Deref,
    sync::atomic::{AtomicU64, Ordering},
};
use zeroize::Zeroizing;

static NEXT_RUST_TARGET_CONTEXT: AtomicU64 = AtomicU64::new(1);

fn next_context_id() -> Result<u64> {
    NEXT_RUST_TARGET_CONTEXT
        .try_update(Ordering::Relaxed, Ordering::Relaxed, |value| {
            value.checked_add(1).filter(|next| *next != 0)
        })
        .map_err(|_| Error::ResourceLimit)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    State,
    ResourceLimit,
    InvalidArtifacts,
    InvalidSource,
    InvalidClientDescriptor,
    Proof(proof::Error),
    Client(client::Error),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::State => f.write_str("nightlean_witness_execution_state"),
            Self::ResourceLimit => f.write_str("nightlean_witness_execution_limit"),
            Self::InvalidArtifacts => f.write_str("nightlean_witness_execution_artifacts"),
            Self::InvalidSource => f.write_str("nightlean_witness_execution_source"),
            Self::InvalidClientDescriptor => {
                f.write_str("nightlean_witness_execution_client_descriptor")
            }
            Self::Proof(error) => error.fmt(f),
            Self::Client(error) => error.fmt(f),
        }
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;

/// JSON returned by source execution. Treat the contents as private, even when the status is
/// public, because completion includes the source result.
pub struct PrivateJson {
    value: Json,
    _reservations: Vec<control::AggregateReservation>,
}
impl PrivateJson {
    fn from_accounted(value: control::AccountedJson) -> Self {
        let (value, reservations) = value.into_parts();
        Self {
            value,
            _reservations: reservations,
        }
    }
    pub fn as_json(&self) -> &Json {
        &self.value
    }
}
impl Deref for PrivateJson {
    type Target = Json;
    fn deref(&self) -> &Self::Target {
        &self.value
    }
}
impl Drop for PrivateJson {
    fn drop(&mut self) {
        control::wipe_json(&mut self.value);
    }
}

struct SecretInputs(BTreeMap<String, Json>);
impl Drop for SecretInputs {
    fn drop(&mut self) {
        for value in self.0.values_mut() {
            control::wipe_json(value);
        }
    }
}

/// A running host-neutral source witness invocation bound to one authenticated bundle target.
pub struct WitnessExecution {
    target: Option<proof::WitnessTarget>,
    session: Option<control::Session>,
    context_id: u64,
    ttl: u64,
    proof_parameters_sha256: String,
    contract_address: String,
    entrypoint: String,
}

impl WitnessExecution {
    /// Authenticate the typed source artifacts, freeze the deployment address, and begin source
    /// execution. `source_inputs` contains the original public and private Lean arguments.
    pub fn begin(
        bundle: &VerifiedBundle,
        state_config: &[u8],
        source_inputs: BTreeMap<String, Json>,
        host_context: host::Context,
        parameters: &TrustedParameters,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        let mut source_inputs = SecretInputs(source_inputs);
        let target =
            proof::WitnessTarget::from_state_config(bundle, state_config, parameters, ttl, rng)
                .map_err(Error::Proof)?;
        Self::from_target(
            bundle,
            target,
            std::mem::take(&mut source_inputs.0),
            host_context,
            parameters,
            ttl,
        )
    }

    /// Begin source execution with a target prepared earlier from the same authenticated bundle.
    /// This lets hosts choose the private-state namespace from the frozen contract address.
    pub fn from_target(
        bundle: &VerifiedBundle,
        target: proof::WitnessTarget,
        source_inputs: BTreeMap<String, Json>,
        host_context: host::Context,
        parameters: &TrustedParameters,
        ttl: u64,
    ) -> Result<Self> {
        let mut source_inputs = SecretInputs(source_inputs);
        let manifest = bundle.authenticated_manifest_sha256().unwrap_or_default();
        if !target.context_matches(manifest, crate::profile::NAME, ttl)
            || target.proof_parameters_sha256() != parameters.sha256()
        {
            return Err(Error::Proof(proof::Error::BindingMismatch));
        }
        let context_id = next_context_id()?;
        let authenticated = target
            .authenticated_control_target(context_id, bundle)
            .map_err(Error::Proof)?;
        let plan_bytes = bundle
            .file(Role::WitnessControl)
            .map_err(|_| Error::InvalidArtifacts)?;
        let session = control::Session::from_authenticated_native_target(
            plan_bytes,
            std::mem::take(&mut source_inputs.0),
            host_context,
            authenticated,
        )
        .map_err(|_| Error::InvalidSource)?;
        Ok(Self {
            contract_address: target.contract_address().to_owned(),
            entrypoint: target.entrypoint().to_owned(),
            target: Some(target),
            session: Some(session),
            context_id,
            ttl,
            proof_parameters_sha256: parameters.sha256().to_owned(),
        })
    }

    pub fn contract_address(&self) -> &str {
        &self.contract_address
    }

    pub fn entrypoint(&self) -> &str {
        &self.entrypoint
    }

    pub fn advance(&mut self) -> Result<PrivateJson> {
        let session = self.session.as_mut().ok_or(Error::State)?;
        session
            .advance_accounted()
            .map(PrivateJson::from_accounted)
            .map_err(|_| Error::InvalidSource)
    }

    pub fn private_request(&mut self) -> Result<PrivateJson> {
        self.session
            .as_mut()
            .ok_or(Error::State)?
            .private_request_accounted()
            .map(PrivateJson::from_accounted)
            .map_err(|_| Error::InvalidSource)
    }

    pub fn resume_typed(&mut self, response: TypedResponse) -> Result<Json> {
        self.session
            .as_mut()
            .ok_or(Error::State)?
            .resume_typed(response)
            .map_err(|_| Error::InvalidSource)
    }

    pub fn cancel(&mut self) -> Result<Json> {
        let result = self
            .session
            .as_mut()
            .ok_or(Error::State)?
            .cancel()
            .map_err(|_| Error::InvalidSource)?;
        self.session = None;
        self.target = None;
        Ok(result)
    }

    /// Prepare from the completed invocation, then consume its Runtime only after all exact
    /// bundle, relation, target and input-map checks pass. A failed preparation leaves this
    /// completed invocation available for a corrected retry without provider re-execution.
    pub fn prepare_proof(
        &mut self,
        bundle: &VerifiedBundle,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<WitnessProof> {
        let target = self.target.as_ref().ok_or(Error::State)?;
        let session = self.session.as_mut().ok_or(Error::State)?;
        if ttl != self.ttl {
            return Err(Error::Proof(proof::Error::BindingMismatch));
        }
        if target.proof_parameters_sha256() != self.proof_parameters_sha256 {
            return Err(Error::Proof(proof::Error::BindingMismatch));
        }
        let authenticated = target
            .authenticated_control_target(self.context_id, bundle)
            .map_err(Error::Proof)?;
        let mut inputs = session
            .peek_completed_invocation(
                self.context_id,
                &authenticated.contract_address,
                &authenticated.entrypoint,
                &authenticated.control_plan,
                &authenticated.binding_bytes,
                &authenticated.relation,
            )
            .map_err(|_| Error::InvalidSource)?;
        let expected_inputs = inputs
            .try_clone_accounted()
            .map_err(|_| Error::ResourceLimit)?;
        let prepared = PreparedProof::from_witness_inputs(
            bundle,
            target,
            std::mem::take(&mut inputs.values),
            ttl,
            rng,
        )
        .map_err(Error::Proof)?;
        let ledger_parameters: ledger::structure::LedgerParameters = serialize::tagged_deserialize(
            bundle
                .file(Role::LedgerParameters)
                .map_err(|_| Error::InvalidArtifacts)?,
        )
        .map_err(|_| Error::InvalidArtifacts)?;
        let deployment = prepared
            .deployment_intent()
            .map(|intent| native_client::prove_deployment(intent, &ledger_parameters))
            .transpose()
            .map_err(|_| Error::InvalidArtifacts)?;
        let completed = session
            .take_completed_invocation(
                self.context_id,
                &authenticated.control_plan,
                &authenticated.binding_bytes,
                &authenticated.relation,
                &expected_inputs,
                &authenticated.contract_address,
                &authenticated.entrypoint,
            )
            .map_err(|_| Error::InvalidSource)?;
        let runtime = completed.runtime;
        self.session = None;
        self.target = None;
        Ok(WitnessProof {
            prepared: Some(prepared),
            deployment,
            runtime: Some(runtime),
            proof_parameters_sha256: self.proof_parameters_sha256.clone(),
            contract_address: self.contract_address.clone(),
            entrypoint: self.entrypoint.clone(),
        })
    }
}

/// A prepared native proof that still owns the exact source Runtime and target.
pub struct WitnessProof {
    prepared: Option<PreparedProof>,
    deployment: Option<ProvedNativeIntent>,
    runtime: Option<host::Runtime>,
    proof_parameters_sha256: String,
    contract_address: String,
    entrypoint: String,
}

impl WitnessProof {
    /// Prove against the frozen source call. Provider or verification errors retain the proof
    /// and Runtime inside this value, so the caller can retry the proof service safely. An
    /// explicit Abort or dropping a polled proof future discards the source Runtime and makes
    /// this value terminal. Dropping a future before its first poll leaves this value untouched.
    pub async fn prove<S: ProofService>(
        &mut self,
        service: &S,
        parameters: &TrustedParameters,
        max_response_bytes: usize,
        stop: impl Future<Output = proof::Abort>,
    ) -> Result<WitnessProvedCall> {
        if self.prepared.is_none() || self.runtime.is_none() {
            return Err(Error::State);
        }
        if parameters.sha256() != self.proof_parameters_sha256 {
            return Err(Error::Proof(proof::Error::InvalidParameters));
        }
        let mut attempt = ProofAttempt {
            owner: self,
            completed: false,
        };
        let result = {
            let prepared = attempt.owner.prepared.as_ref().ok_or(Error::State)?;
            prepared
                .prove(service, parameters, max_response_bytes, stop)
                .await
        };
        match result {
            Ok(proved) => {
                attempt.completed = true;
                attempt.owner.prepared = None;
                Ok(WitnessProvedCall {
                    proved,
                    deployment: attempt.owner.deployment.take(),
                    runtime: attempt.owner.runtime.take(),
                    contract_address: attempt.owner.contract_address.clone(),
                    entrypoint: attempt.owner.entrypoint.clone(),
                    deployment_client_started: false,
                })
            }
            Err(error @ (proof::Error::Cancelled | proof::Error::Deadline)) => {
                attempt.owner.discard();
                attempt.completed = true;
                Err(Error::Proof(error))
            }
            Err(error) => {
                attempt.completed = true;
                Err(Error::Proof(error))
            }
        }
    }

    fn discard(&mut self) {
        self.prepared = None;
        self.deployment = None;
        self.runtime = None;
    }
}

struct ProofAttempt<'a> {
    owner: &'a mut WitnessProof,
    completed: bool,
}
impl Drop for ProofAttempt<'_> {
    fn drop(&mut self) {
        if !self.completed {
            self.owner.discard();
        }
    }
}

/// A proved CALL that keeps the source Runtime private until the native call client consumes it.
pub struct WitnessProvedCall {
    proved: ProvedIntent,
    deployment: Option<ProvedNativeIntent>,
    runtime: Option<host::Runtime>,
    contract_address: String,
    entrypoint: String,
    deployment_client_started: bool,
}

impl WitnessProvedCall {
    pub fn contract_address(&self) -> &str {
        &self.contract_address
    }

    pub fn entrypoint(&self) -> &str {
        &self.entrypoint
    }

    /// Start the separate deployment client. Its Setup context does not consume the source
    /// Runtime, which remains attached to this proved CALL for later execution.
    pub fn start_deployment_client(
        &mut self,
        descriptor_json: &[u8],
        setup_json: &[u8],
    ) -> Result<WitnessClient> {
        if self.deployment_client_started {
            return Err(Error::State);
        }
        let descriptor: Descriptor =
            serde_json::from_slice(descriptor_json).map_err(|_| Error::InvalidClientDescriptor)?;
        let intent = self.deployment.as_ref().ok_or(Error::State)?.clone();
        let driver = Driver::start(
            descriptor,
            setup_json,
            Contract::Deployment {
                intent,
                entrypoint: self.entrypoint.clone(),
            },
        )
        .map_err(Error::Client)?;
        self.deployment_client_started = true;
        Ok(WitnessClient { driver })
    }

    /// Transfer the source Runtime into the client for the proved CALL. Descriptor and target
    /// checks happen before Runtime consumption. A rejected start leaves this object retryable.
    pub fn start_call_client(&mut self, descriptor_json: &[u8]) -> Result<WitnessClient> {
        let descriptor: Descriptor =
            serde_json::from_slice(descriptor_json).map_err(|_| Error::InvalidClientDescriptor)?;
        let contract = Contract::Proved(self.proved.native().clone());
        let driver = Driver::start_with_runtime(descriptor, &mut self.runtime, contract)
            .map_err(Error::Client)?;
        self.runtime = None;
        Ok(WitnessClient { driver })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum WitnessClientCommand {
    Prepare,
    Submit,
    Observe,
    Commit,
    Cancel,
    Deadline,
    Reload,
}

/// A host reply for an existing native client request.
pub enum WitnessClientReply {
    Snapshot(client::Snapshot),
    Funded(UnsealedTransaction),
    Signed(SealedTransaction),
    Submitted(client::Submission),
    Observed(client::Observation),
    Loaded(client::StoredRecord),
    Persisted(client::StoreAcknowledgement),
    Cas(client::CasReceipt),
    Failure,
}

/// One pending native host request. Private payload bytes zeroize on drop.
pub struct WitnessClientRequest {
    pub id: u64,
    pub metadata: Json,
    private_payload: Option<Zeroizing<Vec<u8>>>,
}
impl WitnessClientRequest {
    pub fn private_payload(&self) -> Option<&[u8]> {
        self.private_payload.as_deref().map(Vec::as_slice)
    }
}

/// Thin Rust facade over the existing native client driver. It adds no transaction state machine.
pub struct WitnessClient {
    driver: Driver,
}
impl WitnessClient {
    pub fn status(&self) -> Json {
        self.driver.status()
    }

    pub fn request(&self) -> Result<Option<WitnessClientRequest>> {
        let Some(request) = self.driver.request() else {
            return Ok(None);
        };
        let metadata = request.metadata();
        let private_payload = if metadata["hasPrivateArguments"] == true {
            Some(request.private_bytes().map_err(Error::Client)?)
        } else {
            None
        };
        Ok(Some(WitnessClientRequest {
            id: request.id,
            metadata,
            private_payload,
        }))
    }

    pub fn command(&mut self, command: WitnessClientCommand) -> Result<Json> {
        let command = match command {
            WitnessClientCommand::Prepare => Command::Prepare,
            WitnessClientCommand::Submit => Command::Submit,
            WitnessClientCommand::Observe => Command::Observe,
            WitnessClientCommand::Commit => Command::Commit,
            WitnessClientCommand::Cancel => Command::Cancel,
            WitnessClientCommand::Deadline => Command::Deadline,
            WitnessClientCommand::Reload => Command::Reload,
        };
        self.driver.command(command).map_err(Error::Client)?;
        self.driver.poll().map_err(Error::Client)?;
        Ok(self.driver.status())
    }

    pub fn poll(&mut self) -> Result<Json> {
        self.driver.poll().map_err(Error::Client)?;
        Ok(self.driver.status())
    }

    pub fn complete(&mut self, id: u64, reply: WitnessClientReply) -> Result<Json> {
        let reply = match reply {
            WitnessClientReply::Snapshot(value) => ServiceReply::Snapshot(value),
            WitnessClientReply::Funded(value) => ServiceReply::Funded(value),
            WitnessClientReply::Signed(value) => ServiceReply::Signed(value),
            WitnessClientReply::Submitted(value) => ServiceReply::Submitted(value),
            WitnessClientReply::Observed(value) => ServiceReply::Observed(value),
            WitnessClientReply::Loaded(value) => ServiceReply::Loaded(value),
            WitnessClientReply::Persisted(value) => ServiceReply::Persisted(value),
            WitnessClientReply::Cas(value) => ServiceReply::Cas(value),
            WitnessClientReply::Failure => ServiceReply::Failure,
        };
        self.driver.complete(id, reply).map_err(Error::Client)?;
        self.driver.poll().map_err(Error::Client)?;
        Ok(self.driver.status())
    }

    pub fn detachable(&self) -> bool {
        self.driver.detachable()
    }
}
