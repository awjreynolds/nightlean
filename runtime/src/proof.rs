//! Native proof service boundary. Public artifacts stay retained, private values have no Debug.
//! This API proves a frozen single-call intent. It does not fund, sign, or submit transactions.
use crate::{
    Db, Plan,
    artifacts::{ContractBundleSet, Role, VerifiedBundle},
    assembly::NativeIntent,
    zkir::IrSource,
};
use base_crypto::cost_model::CostDuration;
use futures::{Future, FutureExt, pin_mut, select_biased};
use ledger::structure::{
    ContractAction, ContractCall, Intent, LedgerParameters, ProofMarker, ProofPreimageMarker,
    ProofPreimageVersioned, ProofVersioned, Signature,
};
use midnight_proofs::{plonk::ConstraintSystem, poly::kzg::params::ParamsKZG, utils::SerdeFormat};
use midnight_zk_stdlib::{MidnightPK, Relation, ZkStdLib, ZkStdLibArch};
use onchain_runtime::state::{ContractOperation, ContractState};
use rand::{CryptoRng, Rng};
use serde_json::Value as Json;
use serialize::{Deserializable, Serializable, Tagged, tagged_deserialize, tagged_serialize};
use sha2::{Digest, Sha256};
use std::{cell::RefCell, collections::BTreeMap, fmt, io, rc::Rc, sync::Arc};
use transient_crypto::{
    commitment::{Pedersen, PedersenRandomness},
    curve::Fr,
    proofs::{
        KeyLocation, ParamsProver, ParamsProverProvider, ParamsVerifier, Proof, ProofPreimage,
        ProverKey, ProvingKeyMaterial, ProvingProvider, Resolver, VerifierKey, Zkir,
    },
};

pub type ProvedNativeIntent = Intent<Signature, ProofMarker, PedersenRandomness, Db>;
pub type PublicProvedNativeIntent = Intent<Signature, ProofMarker, Pedersen, Db>;
const MAX_RESPONSE: usize = 1_048_576;
const MAX_PARAMETERS: usize = 134_217_728;
const MAX_PRIVATE_CONFIG: usize = 1_048_576;
const MAX_NATIVE_STATE: usize = 1_048_576;

struct CallPreview {
    call: ContractCall<ProofPreimageMarker, Db>,
    statement: Vec<Fr>,
}

fn preview_transcript_activity(
    old: &onchain_runtime::transcript::Transcript<Db>,
    activity: &[Option<usize>],
    cursor: &mut usize,
    cost_model: &onchain_runtime::cost_model::CostModel,
) -> Result<onchain_runtime::transcript::Transcript<Db>> {
    let mut program = Vec::new();
    for op in old.program.iter_deref() {
        while let Some(Some(skip)) = activity.get(*cursor) {
            let skip = u32::try_from(*skip).map_err(|_| Error::UnsupportedActivity)?;
            program.push(onchain_runtime::ops::Op::Noop { n: skip });
            *cursor = (*cursor).checked_add(1).ok_or(Error::UnsupportedActivity)?;
        }
        if !matches!(activity.get(*cursor), Some(None)) {
            return Err(Error::UnsupportedActivity);
        }
        program.push((*op).clone());
        *cursor = (*cursor).checked_add(1).ok_or(Error::UnsupportedActivity)?;
    }
    while let Some(Some(skip)) = activity.get(*cursor) {
        let skip = u32::try_from(*skip).map_err(|_| Error::UnsupportedActivity)?;
        program.push(onchain_runtime::ops::Op::Noop { n: skip });
        *cursor = (*cursor).checked_add(1).ok_or(Error::UnsupportedActivity)?;
    }

    let mut merged = Vec::with_capacity(program.len());
    let mut pending_noop = 0u32;
    let mut added_gas = 0u64;
    for op in program {
        match op {
            onchain_runtime::ops::Op::Noop { n } => {
                pending_noop = pending_noop
                    .checked_add(n)
                    .ok_or(Error::UnsupportedActivity)?;
            }
            op => {
                if pending_noop != 0 {
                    added_gas = added_gas
                        .checked_add(noop_gas(cost_model, pending_noop)?)
                        .ok_or(Error::UnsupportedActivity)?;
                    merged.push(onchain_runtime::ops::Op::Noop { n: pending_noop });
                    pending_noop = 0;
                }
                merged.push(op);
            }
        }
    }
    if pending_noop != 0 {
        added_gas = added_gas
            .checked_add(noop_gas(cost_model, pending_noop)?)
            .ok_or(Error::UnsupportedActivity)?;
        merged.push(onchain_runtime::ops::Op::Noop { n: pending_noop });
    }
    let original_gas = old.gas.compute_time.into_picoseconds();
    let compute_time = original_gas
        .checked_add(added_gas)
        .ok_or(Error::UnsupportedActivity)?;
    let mut transcript = old.clone();
    transcript.program = merged.into();
    transcript.gas.compute_time = CostDuration::from_picoseconds(compute_time);
    Ok(transcript)
}

fn noop_gas(cost_model: &onchain_runtime::cost_model::CostModel, count: u32) -> Result<u64> {
    let linear = cost_model
        .noop_coeff_arg
        .into_picoseconds()
        .checked_mul(u64::from(count))
        .ok_or(Error::UnsupportedActivity)?;
    cost_model
        .noop_constant
        .into_picoseconds()
        .checked_add(linear)
        .ok_or(Error::UnsupportedActivity)
}

fn preview_call_activity(
    call: &ContractCall<ProofPreimageMarker, Db>,
    activity: &[Option<usize>],
    binding_commitment: Pedersen,
    cost_model: &onchain_runtime::cost_model::CostModel,
) -> Result<CallPreview> {
    let op_count = call
        .guaranteed_transcript
        .iter()
        .chain(call.fallible_transcript.iter())
        .try_fold(0usize, |count, transcript| {
            count.checked_add(transcript.program.len())
        })
        .ok_or(Error::UnsupportedActivity)?;
    if activity.iter().filter(|entry| entry.is_none()).count() != op_count {
        return Err(Error::UnsupportedActivity);
    }
    let mut call = call.clone();
    let mut cursor = 0usize;
    if let Some(old) = call.guaranteed_transcript.as_ref() {
        call.guaranteed_transcript = Some(storage::arena::Sp::new(preview_transcript_activity(
            old,
            activity,
            &mut cursor,
            cost_model,
        )?));
    }
    if let Some(old) = call.fallible_transcript.as_ref() {
        call.fallible_transcript = Some(storage::arena::Sp::new(preview_transcript_activity(
            old,
            activity,
            &mut cursor,
            cost_model,
        )?));
    }
    if cursor != activity.len() {
        return Err(Error::UnsupportedActivity);
    }
    let statement = call
        .public_inputs(binding_commitment)
        .map_err(|_| Error::InvalidIntent)?;
    Ok(CallPreview { call, statement })
}

#[derive(serde::Deserialize)]
#[serde(deny_unknown_fields)]
struct StateOnly {
    state: BTreeMap<String, Json>,
}
impl Drop for StateOnly {
    fn drop(&mut self) {
        for value in self.state.values_mut() {
            crate::control::wipe_json(value);
        }
    }
}

struct SecretInputs(BTreeMap<String, Json>);
impl Drop for SecretInputs {
    fn drop(&mut self) {
        for value in self.0.values_mut() {
            crate::control::wipe_json(value);
        }
    }
}

struct SecretConfig(crate::Config);
impl Drop for SecretConfig {
    fn drop(&mut self) {
        for value in self.0.inputs.values_mut() {
            crate::control::wipe_json(value);
        }
    }
}

/// A one-use target made before source witness execution. The exact deployment nonce and
/// initial state stay with this value so the later call cannot select a different address.
pub struct WitnessTarget {
    manifest: String,
    contract: String,
    entrypoint: String,
    circuit_file: String,
    k: u8,
    proof_parameters_sha256: String,
    ttl: u64,
    deployment: crate::assembly::PreparedDeployment,
}

/// Authenticated complete operation map and its one retained deployment identity.
/// Per-operation parameters and call TTLs are selected separately.
pub struct WitnessContractTarget {
    inner: Arc<WitnessContractInner>,
}

struct WitnessContractInner {
    bundles: ContractBundleSet,
    deployment: crate::assembly::PreparedOperationMapDeployment,
    deployment_identity: String,
    state_schema_sha256: String,
}

/// An operation-specific target. It binds its own circuit degree and trusted SRS before
/// source callbacks begin, while sharing the original deployment address and operation map.
pub struct ContractOperationTarget {
    inner: Arc<WitnessContractInner>,
    operation: String,
    manifest: String,
    k: u8,
    proof_parameters_sha256: String,
    ttl: u64,
}

/// Opaque current state admitted by the native client after its receipt and private commit.
/// The token is moved into one source invocation and cannot be cloned or reconstructed publicly.
pub struct CurrentStateContext {
    contract_set_identity: String,
    deployment_identity: String,
    state_schema_sha256: String,
    address: String,
    identity: String,
    state_bytes: Vec<u8>,
    state: ContractState<Db>,
}

/// Private binding carried from prepared source call through client receipt validation.
#[derive(Clone)]
pub(crate) struct ContractStateBinding {
    contract_set_identity: String,
    deployment_identity: String,
    state_schema_sha256: String,
    address: String,
    operation: String,
    context_identity: String,
    current_state_sha256: Option<String>,
    current_state: Option<Vec<u8>>,
    expected_state: Vec<u8>,
    deployment: bool,
}

impl WitnessContractTarget {
    /// Authenticate every retained operation verifier and freeze one complete-map deployment.
    pub fn from_state_config(
        bundles: ContractBundleSet,
        state_config: &[u8],
        deployment_ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        if state_config.len() > MAX_PRIVATE_CONFIG {
            return Err(Error::Limit);
        }
        let state: StateOnly =
            serde_json::from_slice(state_config).map_err(|_| Error::InvalidPrivateInput)?;
        let (first_name, first_bundle) = bundles.iter().next().ok_or(Error::InvalidArtifacts)?;
        let plan_bytes = first_bundle
            .file(Role::Plan)
            .map_err(|_| Error::InvalidArtifacts)?;
        let plan: Plan = serde_json::from_slice(plan_bytes).map_err(|_| Error::InvalidArtifacts)?;
        let plan_json: Json =
            serde_json::from_slice(plan_bytes).map_err(|_| Error::InvalidArtifacts)?;
        let contract = plan_json["contractName"]
            .as_str()
            .filter(|name| *name == bundles.contract_name())
            .ok_or(Error::BindingMismatch)?;
        if plan.entrypoint != first_name {
            return Err(Error::BindingMismatch);
        }
        let schema_bytes =
            serde_json::to_vec(&plan_json["state"]).map_err(|_| Error::InvalidArtifacts)?;
        let state_schema_sha256 = hex::encode(Sha256::digest(&schema_bytes));

        let expected_operations = bundles
            .iter()
            .map(|(name, _)| name.to_owned())
            .collect::<Vec<_>>();
        let mut operations = Vec::with_capacity(expected_operations.len());
        for (name, bundle) in bundles.iter() {
            let material = Material::retained(bundle)?;
            let selected_plan: Json = serde_json::from_slice(
                bundle
                    .file(Role::Plan)
                    .map_err(|_| Error::InvalidArtifacts)?,
            )
            .map_err(|_| Error::InvalidArtifacts)?;
            if material.entrypoint != name
                || selected_plan["contractName"] != contract
                || selected_plan["entrypoint"] != name
                || serde_json::to_vec(&selected_plan["state"])
                    .map_err(|_| Error::InvalidArtifacts)?
                    != schema_bytes
            {
                return Err(Error::BindingMismatch);
            }
            operations.push((
                name.to_owned(),
                ContractOperation::new(Some(material.verifier), None),
            ));
        }
        let deployment = crate::assembly::prepare_operation_map_deployment_target(
            &plan,
            contract,
            &state.state,
            &expected_operations,
            operations,
            deployment_ttl,
            rng,
        )
        .map_err(|_| Error::InvalidPrivateInput)?;
        let deployment_identity = hex::encode(Sha256::digest(encode(deployment.intent())?));
        Ok(Self {
            inner: Arc::new(WitnessContractInner {
                bundles,
                deployment,
                deployment_identity,
                state_schema_sha256,
            }),
        })
    }

    pub fn contract_address(&self) -> &str {
        self.inner.deployment.address()
    }

    pub fn identity(&self) -> &str {
        self.inner.bundles.identity()
    }

    /// Select one operation with its own trusted parameters and fresh native call TTL.
    pub fn operation(
        &self,
        operation: &str,
        parameters: &TrustedParameters,
        ttl: u64,
    ) -> Result<ContractOperationTarget> {
        if ttl == 0 {
            return Err(Error::InvalidIntent);
        }
        let bundle = self
            .inner
            .bundles
            .operation(operation)
            .ok_or(Error::BindingMismatch)?;
        let material = Material::retained(bundle)?;
        if material.entrypoint != operation || material.circuit.k() != parameters.k() {
            return Err(Error::InvalidParameters);
        }
        let plan: Json = serde_json::from_slice(
            bundle
                .file(Role::Plan)
                .map_err(|_| Error::InvalidArtifacts)?,
        )
        .map_err(|_| Error::InvalidArtifacts)?;
        if plan["contractName"] != self.inner.bundles.contract_name()
            || plan["entrypoint"] != operation
        {
            return Err(Error::BindingMismatch);
        }
        Ok(ContractOperationTarget {
            inner: self.inner.clone(),
            operation: operation.to_owned(),
            manifest: bundle
                .authenticated_manifest_sha256()
                .ok_or(Error::UnauthenticatedBundle)?
                .to_owned(),
            k: material.circuit.k(),
            proof_parameters_sha256: parameters.sha256().to_owned(),
            ttl,
        })
    }

    pub(crate) fn deployment_intent(&self) -> &NativeIntent {
        self.inner.deployment.intent()
    }

    pub(crate) fn deployment_bundle(&self) -> Result<&VerifiedBundle> {
        self.inner
            .bundles
            .iter()
            .next()
            .map(|(_, bundle)| bundle)
            .ok_or(Error::InvalidArtifacts)
    }

    pub(crate) fn deployment_binding(&self, operation: &str) -> Result<ContractStateBinding> {
        let bundle = self
            .inner
            .bundles
            .operation(operation)
            .ok_or(Error::BindingMismatch)?;
        let deployment = self
            .inner
            .deployment
            .intent()
            .actions
            .iter_deref()
            .next()
            .ok_or(Error::InvalidIntent)?;
        let ContractAction::Deploy(deployment) = deployment else {
            return Err(Error::InvalidIntent);
        };
        let expected_state = encode(&deployment.initial_state)?;
        Ok(ContractStateBinding {
            contract_set_identity: self.identity().to_owned(),
            deployment_identity: self.inner.deployment_identity.clone(),
            state_schema_sha256: self.inner.state_schema_sha256.clone(),
            address: self.contract_address().to_owned(),
            operation: operation.to_owned(),
            context_identity: digest_parts(&[
                self.identity().as_bytes(),
                self.inner.deployment_identity.as_bytes(),
                operation.as_bytes(),
                bundle
                    .authenticated_manifest_sha256()
                    .ok_or(Error::UnauthenticatedBundle)?
                    .as_bytes(),
            ]),
            current_state_sha256: None,
            current_state: None,
            expected_state,
            deployment: true,
        })
    }
}

impl ContractOperationTarget {
    pub fn operation(&self) -> &str {
        &self.operation
    }

    pub fn contract_address(&self) -> &str {
        self.inner.deployment.address()
    }

    pub(crate) fn bundle(&self) -> Result<&VerifiedBundle> {
        self.inner
            .bundles
            .operation(&self.operation)
            .ok_or(Error::BindingMismatch)
    }

    pub(crate) fn authenticated_control_target(
        &self,
        context_id: u64,
    ) -> Result<crate::control::AuthenticatedNativeTarget> {
        let bundle = self.bundle()?;
        if bundle.authenticated_manifest_sha256() != Some(self.manifest.as_str()) {
            return Err(Error::BindingMismatch);
        }
        let target = authenticated_control_target(
            context_id,
            bundle,
            &self.inner.bundles.contract_name(),
            &self.operation,
            bundle
                .manifest()
                .entries
                .iter()
                .find(|entry| entry.role == Role::Circuit)
                .map(|entry| entry.name.as_str())
                .ok_or(Error::InvalidArtifacts)?,
            self.contract_address(),
        )?;
        Ok(target)
    }

    pub(crate) fn context_matches(&self, state: &CurrentStateContext) -> bool {
        let Ok(initial) = deployment_operations(self.inner.deployment.intent()) else {
            return false;
        };
        state.contract_set_identity == self.inner.bundles.identity()
            && state.deployment_identity == self.inner.deployment_identity
            && state.state_schema_sha256 == self.inner.state_schema_sha256
            && state.address == self.contract_address()
            && state.state.operations == initial.operations
    }

    pub(crate) fn parameters_sha256(&self) -> &str {
        &self.proof_parameters_sha256
    }

    pub(crate) fn ttl(&self) -> u64 {
        self.ttl
    }

    pub(crate) fn k(&self) -> u8 {
        self.k
    }

    pub(crate) fn contract_set_identity(&self) -> &str {
        self.inner.bundles.identity()
    }

    pub(crate) fn deployment_identity(&self) -> &str {
        &self.inner.deployment_identity
    }

    pub(crate) fn state_schema_sha256(&self) -> &str {
        &self.inner.state_schema_sha256
    }

    fn selected_material(&self) -> Result<Material> {
        let material = Material::retained(self.bundle()?)?;
        if material.entrypoint != self.operation || material.circuit.k() != self.k {
            return Err(Error::BindingMismatch);
        }
        Ok(material)
    }
}

impl ContractStateBinding {
    /// Native client calls this only after BoundTransaction receipt validation, exact state
    /// comparison, finality, and the required private journal commit.
    pub(crate) fn admit_committed_state(
        &self,
        state_bytes: &[u8],
        expected_state: &[u8],
        checkpoint_identity: &str,
        deployment: bool,
    ) -> Result<CurrentStateContext> {
        let current_state_sha256 = self
            .current_state
            .as_deref()
            .map(|current| hex::encode(Sha256::digest(current)));
        if state_bytes.len() > MAX_NATIVE_STATE
            || state_bytes != expected_state
            || state_bytes != self.expected_state
            || deployment != self.deployment
            || checkpoint_identity.len() != 64
            || (!self.deployment
                && current_state_sha256.as_deref() != self.current_state_sha256.as_deref())
            || !checkpoint_identity
                .bytes()
                .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte))
        {
            return Err(Error::BindingMismatch);
        }
        let state: ContractState<Db> = decode(state_bytes)?;
        if encode(&state)? != state_bytes {
            return Err(Error::BindingMismatch);
        }
        let state_sha256 = hex::encode(Sha256::digest(state_bytes));
        let identity = digest_parts(&[
            self.contract_set_identity.as_bytes(),
            self.deployment_identity.as_bytes(),
            self.address.as_bytes(),
            self.state_schema_sha256.as_bytes(),
            state_sha256.as_bytes(),
            checkpoint_identity.as_bytes(),
        ]);
        Ok(CurrentStateContext {
            contract_set_identity: self.contract_set_identity.clone(),
            deployment_identity: self.deployment_identity.clone(),
            state_schema_sha256: self.state_schema_sha256.clone(),
            address: self.address.clone(),
            identity,
            state_bytes: state_bytes.to_vec(),
            state,
        })
    }

    pub(crate) fn current_state_bytes(&self) -> Option<&[u8]> {
        self.current_state.as_deref()
    }

    pub(crate) fn context_identity(&self) -> &str {
        &self.context_identity
    }

    pub(crate) fn matches_event(&self, deployment: bool) -> bool {
        self.deployment == deployment
    }

    pub(crate) fn matches_target(&self, address: &str, operation: &str) -> bool {
        self.address == address && self.operation == operation
    }
}

fn digest_parts(parts: &[&[u8]]) -> String {
    let mut hash = Sha256::new();
    for part in parts {
        hash.update((part.len() as u64).to_le_bytes());
        hash.update(part);
    }
    hex::encode(hash.finalize())
}

fn deployment_operations(intent: &NativeIntent) -> Result<ContractState<Db>> {
    let Some(ContractAction::Deploy(deployment)) = intent.actions.iter_deref().next() else {
        return Err(Error::InvalidIntent);
    };
    Ok(deployment.initial_state.clone())
}

fn authenticated_control_target(
    context_id: u64,
    bundle: &VerifiedBundle,
    contract: &str,
    entrypoint: &str,
    circuit_file: &str,
    address: &str,
) -> Result<crate::control::AuthenticatedNativeTarget> {
    let control_plan_bytes = bundle
        .file(Role::WitnessControl)
        .map_err(|_| Error::InvalidArtifacts)?
        .to_vec();
    let control_plan: Json =
        serde_json::from_slice(&control_plan_bytes).map_err(|_| Error::InvalidArtifacts)?;
    let binding_bytes = bundle
        .file(Role::WitnessBinding)
        .map_err(|_| Error::InvalidArtifacts)?
        .to_vec();
    let relation: Json = serde_json::from_slice(
        bundle
            .file(Role::Circuit)
            .map_err(|_| Error::InvalidArtifacts)?,
    )
    .map_err(|_| Error::InvalidArtifacts)?;
    let selected_plan: Json = serde_json::from_slice(
        bundle
            .file(Role::Plan)
            .map_err(|_| Error::InvalidArtifacts)?,
    )
    .map_err(|_| Error::InvalidArtifacts)?;
    if selected_plan["contractName"] != contract
        || selected_plan["entrypoint"] != entrypoint
        || selected_plan["nativeCircuitFile"] != circuit_file
    {
        return Err(Error::BindingMismatch);
    }
    crate::control::validate_witness_artifacts(
        &control_plan,
        &binding_bytes,
        &relation,
        contract,
        entrypoint,
        circuit_file,
        crate::profile::NAME,
    )
    .map_err(|_| Error::BindingMismatch)?;
    Ok(crate::control::AuthenticatedNativeTarget {
        context_id,
        contract_address: address.to_owned(),
        entrypoint: entrypoint.to_owned(),
        control_plan,
        control_plan_bytes,
        binding_bytes,
        relation,
    })
}

impl WitnessTarget {
    /// Prepare the exact deployment target from authenticated public artifacts and private
    /// initial state. This runs before provider calls and returns only a public target identity.
    pub fn from_state_config(
        bundle: &VerifiedBundle,
        state_config: &[u8],
        parameters: &TrustedParameters,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        if state_config.len() > MAX_PRIVATE_CONFIG {
            return Err(Error::Limit);
        }
        let manifest = bundle
            .authenticated_manifest_sha256()
            .ok_or(Error::UnauthenticatedBundle)?
            .to_owned();
        let material = Material::retained(bundle)?;
        if material.circuit.k() != parameters.k() {
            return Err(Error::InvalidParameters);
        }
        let state: StateOnly =
            serde_json::from_slice(state_config).map_err(|_| Error::InvalidPrivateInput)?;
        let plan_bytes = bundle
            .file(Role::Plan)
            .map_err(|_| Error::InvalidArtifacts)?;
        let plan: Plan = serde_json::from_slice(plan_bytes).map_err(|_| Error::InvalidArtifacts)?;
        let plan_json: Json =
            serde_json::from_slice(plan_bytes).map_err(|_| Error::InvalidArtifacts)?;
        let contract = plan_json["contractName"]
            .as_str()
            .filter(|name| !name.is_empty())
            .ok_or(Error::InvalidArtifacts)?
            .to_owned();
        let circuit_file = bundle
            .manifest()
            .entries
            .iter()
            .find(|entry| entry.role == Role::Circuit)
            .map(|entry| entry.name.clone())
            .ok_or(Error::InvalidArtifacts)?;
        let deployment = crate::assembly::prepare_deployment_target(
            &plan,
            &state.state,
            material.verifier,
            ttl,
            rng,
        )
        .map_err(|_| Error::InvalidPrivateInput)?;
        let target = Self {
            manifest,
            contract,
            entrypoint: plan.entrypoint,
            circuit_file,
            k: material.circuit.k(),
            proof_parameters_sha256: parameters.sha256().to_owned(),
            ttl,
            deployment,
        };
        target.authenticated_control_target(0, bundle)?;
        Ok(target)
    }

    pub(crate) fn context_matches(&self, manifest: &str, profile: &str, ttl: u64) -> bool {
        self.manifest == manifest && profile == crate::profile::NAME && self.ttl == ttl
    }

    pub(crate) fn manifest_sha256(&self) -> &str {
        &self.manifest
    }

    pub fn contract_address(&self) -> &str {
        &self.deployment.address
    }

    pub fn entrypoint(&self) -> &str {
        &self.entrypoint
    }

    pub(crate) fn k(&self) -> u8 {
        self.k
    }

    pub(crate) fn proof_parameters_sha256(&self) -> &str {
        &self.proof_parameters_sha256
    }

    pub(crate) fn authenticated_control_target(
        &self,
        context_id: u64,
        bundle: &VerifiedBundle,
    ) -> Result<crate::control::AuthenticatedNativeTarget> {
        if bundle.authenticated_manifest_sha256() != Some(self.manifest.as_str()) {
            return Err(Error::BindingMismatch);
        }
        authenticated_control_target(
            context_id,
            bundle,
            &self.contract,
            &self.entrypoint,
            &self.circuit_file,
            self.contract_address(),
        )
    }
}

/// Fixed diagnostics deliberately discard upstream value-bearing causes.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    UnauthenticatedBundle,
    InvalidArtifacts,
    Limit,
    InvalidPrivateInput,
    InvalidIntent,
    UnsupportedActivity,
    InvalidParameters,
    Service,
    InvalidResponse,
    InvalidProof,
    BindingMismatch,
    Cancelled,
    Deadline,
    Attachment,
}
impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "nightlean_proof_{self:?}")
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;
fn decode<T: Deserializable + Tagged>(data: &[u8]) -> Result<T> {
    let mut reader = data;
    let value = tagged_deserialize(&mut reader).map_err(|_| Error::InvalidArtifacts)?;
    if !reader.is_empty() {
        return Err(Error::InvalidArtifacts);
    }
    Ok(value)
}
fn encode<T: Serializable + Tagged>(value: &T) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    tagged_serialize(value, &mut bytes).map_err(|_| Error::Attachment)?;
    Ok(bytes)
}

fn take<'a>(reader: &mut &'a [u8], len: usize) -> Result<&'a [u8]> {
    let (value, rest) = reader
        .split_at_checked(len)
        .ok_or(Error::InvalidArtifacts)?;
    *reader = rest;
    Ok(value)
}
fn key_payload<T: Tagged>(bytes: &[u8]) -> Result<&[u8]> {
    let prefix = format!("midnight:{}:", T::tag());
    let mut reader = bytes
        .strip_prefix(prefix.as_bytes())
        .ok_or(Error::InvalidArtifacts)?;
    let len = <u32 as Deserializable>::deserialize(&mut reader, 0)
        .map_err(|_| Error::InvalidArtifacts)? as usize;
    if len != reader.len() || len > MAX_PARAMETERS {
        return Err(Error::InvalidArtifacts);
    }
    Ok(reader)
}
fn key_columns(circuit: &IrSource, k: u8) -> Result<(usize, usize)> {
    if !(1..=20).contains(&k) {
        return Err(Error::InvalidArtifacts);
    }
    let mut cs = ConstraintSystem::default();
    ZkStdLib::configure(&mut cs, (circuit.used_chips(), k - 1));
    Ok((
        cs.num_fixed_columns() + cs.num_selectors(),
        cs.permutation().get_columns().len(),
    ))
}
fn check_vk_body(
    reader: &mut &[u8],
    k: u8,
    point_bytes: usize,
    columns: (usize, usize),
) -> Result<()> {
    if take(reader, 2)? != [3, k] {
        return Err(Error::InvalidArtifacts);
    }
    let count = u32::from_le_bytes(take(reader, 4)?.try_into().unwrap()) as usize;
    if count != columns.0 {
        return Err(Error::InvalidArtifacts);
    }
    take(reader, (count + columns.1) * point_bytes)?;
    Ok(())
}
fn checked_prover(
    bytes: &[u8],
    circuit: &IrSource,
    k: u8,
    columns: (usize, usize),
) -> Result<ProverKey<IrSource>> {
    let raw = key_payload::<ProverKey<IrSource>>(bytes)?;
    let mut prefix = vec![k];
    circuit
        .write_relation(&mut prefix)
        .map_err(|_| Error::InvalidArtifacts)?;
    // Reject arbitrary embedded relations before the native parser configures their chips.
    let mut reader = raw
        .strip_prefix(prefix.as_slice())
        .ok_or(Error::InvalidArtifacts)?;
    check_vk_body(&mut reader, k, 96, columns)?;
    for expected in [columns.0, columns.1] {
        let count = u32::from_be_bytes(take(&mut reader, 4)?.try_into().unwrap()) as usize;
        if count != expected {
            return Err(Error::InvalidArtifacts);
        }
        for _ in 0..count {
            let len = u32::from_be_bytes(take(&mut reader, 4)?.try_into().unwrap()) as usize;
            if len != 1usize << k {
                return Err(Error::InvalidArtifacts);
            }
            // The pinned Fq raw reader omits its modulus check, even in RawBytes mode.
            // Montgomery limbs still require the same [0, modulus) numeric bound.
            if take(&mut reader, len * 32)?
                .chunks_exact(32)
                .any(|scalar| Fr::from_le_bytes(scalar).is_none())
            {
                return Err(Error::InvalidArtifacts);
            }
        }
    }
    if !reader.is_empty() {
        return Err(Error::InvalidArtifacts);
    }
    let mut reader = raw;
    let key = MidnightPK::<IrSource>::read(&mut reader, SerdeFormat::RawBytes)
        .map_err(|_| Error::InvalidArtifacts)?;
    if !reader.is_empty() {
        return Err(Error::InvalidArtifacts);
    }
    Ok(ProverKey::from_raw(key))
}
fn checked_verifier(
    bytes: &[u8],
    circuit: &IrSource,
    k: u8,
    columns: (usize, usize),
) -> Result<VerifierKey> {
    let mut reader = key_payload::<VerifierKey>(bytes)?;
    let architecture = ZkStdLibArch::read(&mut reader).map_err(|_| Error::InvalidArtifacts)?;
    if architecture != circuit.used_chips() || take(&mut reader, 1)? != [k] {
        return Err(Error::InvalidArtifacts);
    }
    let inputs = u32::from_le_bytes(take(&mut reader, 4)?.try_into().unwrap());
    if inputs == 0 || inputs > (1u32 << k) {
        return Err(Error::InvalidArtifacts);
    }
    check_vk_body(&mut reader, k, 48, columns)?;
    if !reader.is_empty() {
        return Err(Error::InvalidArtifacts);
    }
    let verifier: VerifierKey = decode(bytes)?;
    verifier.init().map_err(|_| Error::InvalidArtifacts)?;
    Ok(verifier)
}

/// The host supplies trusted SRS identity independently of untrusted provider responses.
/// A matching digest authenticates bytes, not their ceremony or provenance.
pub struct TrustedParameters {
    k: u8,
    sha256: String,
    prover: ParamsProver,
    verifier: ParamsVerifier,
}
impl TrustedParameters {
    pub fn from_bytes(bytes: &[u8], k: u8, trusted_sha256: &str) -> Result<Self> {
        if bytes.is_empty() || bytes.len() > MAX_PARAMETERS {
            return Err(Error::Limit);
        }
        if !(1..=20).contains(&k)
            || trusted_sha256.len() != 64
            || !trusted_sha256
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            || hex::encode(Sha256::digest(bytes)) != trusted_sha256
        {
            return Err(Error::InvalidParameters);
        }
        // The pinned native raw format has two 2^k G1 arrays (96 bytes each),
        // two G2 points (192 bytes each), and a little-endian u32 degree.
        // Check before the upstream parser shifts or allocates from its header.
        let expected_len = 4 + (1usize << k) * 2 * 96 + 2 * 192;
        if bytes.len() != expected_len || bytes[..4] != u32::from(k).to_le_bytes() {
            return Err(Error::InvalidParameters);
        }
        let mut reader = bytes;
        let native = ParamsKZG::read_custom(&mut reader, SerdeFormat::RawBytes)
            .map_err(|_| Error::InvalidParameters)?;
        if !reader.is_empty() {
            return Err(Error::InvalidParameters);
        }
        let prover = ParamsProver(Arc::new(native));
        // ParamsVerifier exposes only the unchecked reader. All points and the
        // complete encoding have already passed the checked native parser above.
        let verifier = ParamsVerifier::read(bytes).map_err(|_| Error::InvalidParameters)?;
        Ok(Self {
            k,
            sha256: trusted_sha256.to_owned(),
            prover,
            verifier,
        })
    }
    pub fn k(&self) -> u8 {
        self.k
    }
    pub fn sha256(&self) -> &str {
        &self.sha256
    }
}
impl ParamsProverProvider for TrustedParameters {
    async fn get_params(&self, k: u8) -> io::Result<ParamsProver> {
        if k != self.k {
            return Err(io::Error::other("nightlean_parameter_degree_mismatch"));
        }
        Ok(self.prover.clone())
    }
}

struct Material {
    native: ProvingKeyMaterial,
    prover: ProverKey<IrSource>,
    circuit: IrSource,
    verifier: VerifierKey,
    parameters: LedgerParameters,
    entrypoint: String,
}
impl Material {
    fn retained(bundle: &VerifiedBundle) -> Result<Self> {
        if bundle.authenticated_manifest_sha256().is_none() {
            return Err(Error::UnauthenticatedBundle);
        }
        let get = |role| bundle.file(role).map_err(|_| Error::InvalidArtifacts);
        let plan: Plan =
            serde_json::from_slice(get(Role::Plan)?).map_err(|_| Error::InvalidArtifacts)?;
        if !crate::profile::validate_plan(plan.target.as_deref(), plan.target_profile.as_ref()) {
            return Err(Error::InvalidArtifacts);
        }
        let native = ProvingKeyMaterial {
            prover_key: get(Role::ProverKey)?.to_vec(),
            verifier_key: get(Role::VerifierKey)?.to_vec(),
            ir_source: get(Role::Circuit)?.to_vec(),
        };
        let circuit = IrSource::load(&native.ir_source[..]).map_err(|_| Error::InvalidArtifacts)?;
        if !circuit.do_communications_commitment {
            return Err(Error::InvalidArtifacts);
        }
        let k = circuit.k();
        let columns = key_columns(&circuit, k)?;
        let prover = checked_prover(&native.prover_key, &circuit, k, columns)?;
        let verifier = checked_verifier(&native.verifier_key, &circuit, k, columns)?;
        let parameters = decode(get(Role::LedgerParameters)?)?;
        Ok(Self {
            native,
            prover,
            circuit,
            verifier,
            parameters,
            entrypoint: plan.entrypoint,
        })
    }
}

/// Frozen intent and exact native statement. No private preimage accessor or Debug implementation.
pub struct PreparedProof {
    intent: NativeIntent,
    deployment: Option<NativeIntent>,
    material: Material,
    statement: Vec<Fr>,
    activity: Vec<Option<usize>>,
    required_parameters_sha256: Option<String>,
    contract_binding: Option<ContractStateBinding>,
}
impl PreparedProof {
    /// Construct the source-selected call in memory using host-owned cryptographic entropy.
    /// Authentication and public material validation precede private input parsing.
    pub fn from_config(
        bundle: &VerifiedBundle,
        private_config: &[u8],
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        let material = Material::retained(bundle)?;
        if private_config.len() > 1_048_576 {
            return Err(Error::Limit);
        }
        let config =
            crate::parse_private_config(private_config).map_err(|_| Error::InvalidPrivateInput)?;
        let plan: Plan = serde_json::from_slice(
            bundle
                .file(Role::Plan)
                .map_err(|_| Error::InvalidArtifacts)?,
        )
        .map_err(|_| Error::InvalidArtifacts)?;
        let (deploy, intent) = crate::assembly::prepare_call(
            &plan,
            &config,
            &material.parameters,
            material.verifier.clone(),
            &material.circuit,
            ttl,
            rng,
        )
        .map_err(|_| Error::InvalidPrivateInput)?;
        let mut prepared = Self::freeze(material, intent)?;
        prepared.deployment = Some(deploy);
        Ok(prepared)
    }

    /// Prepare a proof from the exact native source input map and retained deployment target.
    /// Callers must obtain `inputs` from a completed authenticated Control invocation.
    pub fn from_witness_inputs(
        bundle: &VerifiedBundle,
        target: &WitnessTarget,
        inputs: BTreeMap<String, Json>,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        let mut inputs = SecretInputs(inputs);
        if !target.context_matches(
            bundle.authenticated_manifest_sha256().unwrap_or_default(),
            crate::profile::NAME,
            ttl,
        ) {
            return Err(Error::BindingMismatch);
        }
        target.authenticated_control_target(0, bundle)?;
        let material = Material::retained(bundle)?;
        if material.circuit.k() != target.k {
            return Err(Error::InvalidParameters);
        }
        let plan: Plan = serde_json::from_slice(
            bundle
                .file(Role::Plan)
                .map_err(|_| Error::InvalidArtifacts)?,
        )
        .map_err(|_| Error::InvalidArtifacts)?;
        let config = SecretConfig(crate::Config {
            inputs: std::mem::take(&mut inputs.0),
            state: BTreeMap::new(),
            negative_cases: Vec::new(),
        });
        let call = crate::assembly::prepare_call_for_target(
            &plan,
            &config.0,
            &material.parameters,
            material.verifier.clone(),
            &material.circuit,
            ttl,
            &target.deployment,
            rng,
        );
        let call = call.map_err(|_| Error::InvalidPrivateInput)?;
        let mut prepared = Self::freeze(material, call)?;
        prepared.deployment = Some(target.deployment.intent.clone());
        prepared.required_parameters_sha256 = Some(target.proof_parameters_sha256.clone());
        let (address, entrypoint) = prepared.call_target()?;
        if address != target.contract_address() || entrypoint != target.entrypoint() {
            return Err(Error::BindingMismatch);
        }
        Ok(prepared)
    }

    pub(crate) fn from_contract_witness_inputs(
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Json>,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        let mut inputs = SecretInputs(inputs);
        if !target.context_matches(current) {
            return Err(Error::BindingMismatch);
        }
        let material = target.selected_material()?;
        let bundle = target.bundle()?;
        if bundle.authenticated_manifest_sha256() != Some(target.manifest.as_str()) {
            return Err(Error::BindingMismatch);
        }
        let plan: Plan = serde_json::from_slice(
            bundle
                .file(Role::Plan)
                .map_err(|_| Error::InvalidArtifacts)?,
        )
        .map_err(|_| Error::InvalidArtifacts)?;
        let config = SecretConfig(crate::Config {
            inputs: std::mem::take(&mut inputs.0),
            state: BTreeMap::new(),
            negative_cases: Vec::new(),
        });
        let (call, predicted) = crate::assembly::prepare_call_for_current_state(
            &plan,
            &target.inner.bundles.contract_name(),
            &target.operation,
            &config.0,
            &material.parameters,
            ContractOperation::new(Some(material.verifier.clone()), None),
            &material.circuit,
            target.ttl,
            &target.inner.deployment,
            &current.state,
            rng,
        )
        .map_err(|_| Error::InvalidPrivateInput)?;
        let expected_state = encode(&predicted)?;
        let mut prepared = Self::freeze(material, call)?;
        prepared.required_parameters_sha256 = Some(target.proof_parameters_sha256.clone());
        let (address, entrypoint) = prepared.call_target()?;
        if address != target.contract_address() || entrypoint != target.operation {
            return Err(Error::BindingMismatch);
        }
        prepared.contract_binding = Some(ContractStateBinding {
            contract_set_identity: target.contract_set_identity().to_owned(),
            deployment_identity: target.deployment_identity().to_owned(),
            state_schema_sha256: target.state_schema_sha256().to_owned(),
            address,
            operation: entrypoint,
            context_identity: current.identity.clone(),
            current_state_sha256: Some(hex::encode(Sha256::digest(&current.state_bytes))),
            current_state: Some(current.state_bytes.clone()),
            expected_state,
            deployment: false,
        });
        Ok(prepared)
    }

    /// Re-freeze a host-balanced intent. This first slice accepts one call and no offers/dust.
    /// Native intent inputs contain private witnesses and need private storage.
    pub fn from_intent(bundle: &VerifiedBundle, intent: NativeIntent) -> Result<Self> {
        Self::freeze(Material::retained(bundle)?, intent)
    }
    fn freeze(material: Material, intent: NativeIntent) -> Result<Self> {
        if intent.actions.len() != 1
            || intent.dust_actions.is_some()
            || intent.guaranteed_unshielded_offer.is_some()
            || intent.fallible_unshielded_offer.is_some()
        {
            return Err(Error::InvalidIntent);
        }
        let Some(ContractAction::Call(call)) = intent.actions.iter_deref().next() else {
            return Err(Error::InvalidIntent);
        };
        if call.entry_point.0 != material.entrypoint.as_bytes() {
            return Err(Error::InvalidIntent);
        }
        let ProofPreimageVersioned::V2(preimage) = &call.proof else {
            return Err(Error::InvalidIntent);
        };
        if preimage.key_location.0.as_ref() != material.entrypoint {
            return Err(Error::InvalidIntent);
        }
        let activity = preimage
            .check(&material.circuit)
            .map_err(|_| Error::InvalidIntent)?;
        let preview = preview_call_activity(
            call,
            &activity,
            intent.binding_commitment.into(),
            &material.parameters.cost_model.runtime_cost_model,
        )?;
        let statement = preview.statement;
        if statement.get(1) != Some(&call.communication_commitment)
            || preimage
                .communications_commitment
                .map(|(commitment, _)| commitment)
                != Some(call.communication_commitment)
        {
            return Err(Error::BindingMismatch);
        }
        let result = Self {
            intent,
            deployment: None,
            material,
            statement,
            activity,
            required_parameters_sha256: None,
            contract_binding: None,
        };
        result.validate_statement_preimage()?;
        Ok(result)
    }
    fn preimage(&self) -> Result<&ProofPreimage> {
        let Some(ContractAction::Call(call)) = self.intent.actions.iter_deref().next() else {
            return Err(Error::InvalidIntent);
        };
        let ProofPreimageVersioned::V2(preimage) = &call.proof else {
            return Err(Error::InvalidIntent);
        };
        Ok(preimage)
    }
    fn validate_statement_preimage(&self) -> Result<()> {
        let mut preimage = self.preimage()?.clone();
        preimage.binding_input = self.statement[0];
        // The selected IR checks exact input/output packing and communication binding.
        let activity = preimage
            .check(&self.material.circuit)
            .map_err(|_| Error::BindingMismatch)?;
        if activity != self.activity {
            return Err(Error::UnsupportedActivity);
        }
        let Some(ContractAction::Call(call)) = self.intent.actions.iter_deref().next() else {
            return Err(Error::InvalidIntent);
        };
        let preview = preview_call_activity(
            call,
            &activity,
            self.intent.binding_commitment.into(),
            &self.material.parameters.cost_model.runtime_cost_model,
        )?;
        if preview.statement != self.statement {
            return Err(Error::BindingMismatch);
        }
        Ok(())
    }
    pub fn deployment_intent(&self) -> Option<&NativeIntent> {
        self.deployment.as_ref()
    }
    pub(crate) fn call_target(&self) -> Result<(String, String)> {
        let Some(ContractAction::Call(call)) = self.intent.actions.iter_deref().next() else {
            return Err(Error::InvalidIntent);
        };
        let entrypoint =
            String::from_utf8(call.entry_point.0.clone()).map_err(|_| Error::InvalidIntent)?;
        Ok((hex::encode(call.address.0.0), entrypoint))
    }
    pub fn k(&self) -> u8 {
        self.material.circuit.k()
    }
    pub fn profile(&self) -> &'static str {
        crate::profile::NAME
    }
    fn validate_parameters(&self, params: &TrustedParameters) -> Result<()> {
        if params.k != self.k()
            || self
                .required_parameters_sha256
                .as_deref()
                .is_some_and(|digest| digest != params.sha256())
        {
            return Err(Error::InvalidParameters);
        }
        Ok(())
    }
    /// Explicit private serialization for durable retries. Re-proving requires fresh entropy.
    pub fn private_intent_bytes(&self) -> Result<Vec<u8>> {
        encode(&self.intent)
    }
    /// Retain an explicit private service request without retaining a future or callback.
    /// The preimage uses the same frozen binding checked by the native intent prover.
    pub fn private_request_payload(
        &self,
        params: &TrustedParameters,
        max_response_bytes: usize,
    ) -> Result<zeroize::Zeroizing<Vec<u8>>> {
        if max_response_bytes == 0 || max_response_bytes > MAX_RESPONSE {
            return Err(Error::Limit);
        }
        self.validate_parameters(params)?;
        self.validate_statement_preimage()?;
        let mut preimage = self.preimage()?.clone();
        preimage.binding_input = self.statement[0];
        ProofRequest {
            preimage: &preimage,
            material: &self.material.native,
            prover: &self.material.prover,
            parameters: params,
            max_response_bytes,
            expected_statement: &self.statement,
            expected_activity: &self.activity,
        }
        .private_wire_payload()
    }
    /// Resume a pulled service request through the same verifier and native attachment path.
    pub async fn attach_response(
        &self,
        params: &TrustedParameters,
        response: &[u8],
        max_response_bytes: usize,
    ) -> Result<ProvedIntent> {
        struct Supplied<'a>(&'a [u8]);
        impl ProofService for Supplied<'_> {
            async fn prove(
                &self,
                _: ProofRequest<'_>,
            ) -> std::result::Result<Vec<u8>, ServiceError> {
                Ok(self.0.to_vec())
            }
        }
        if response.is_empty() || response.len() > max_response_bytes {
            return Err(Error::Limit);
        }
        self.prove(
            &Supplied(response),
            params,
            max_response_bytes,
            futures::future::pending(),
        )
        .await
    }
    /// Explicit local service adapter for a host worker with fresh host-owned entropy.
    /// Returns the service V2 encoding, separate from the verified attached ledger V3 result.
    pub async fn local_response(
        &self,
        params: &TrustedParameters,
        max_response_bytes: usize,
        rng: impl Rng + CryptoRng,
    ) -> Result<Vec<u8>> {
        let proved = self
            .prove(
                &LocalProver::new(rng),
                params,
                max_response_bytes,
                futures::future::pending(),
            )
            .await?;
        let Some(ContractAction::Call(call)) = proved.native().actions.iter_deref().next() else {
            return Err(Error::Attachment);
        };
        let ProofVersioned::V3(proof) = &call.proof else {
            return Err(Error::Attachment);
        };
        encode(&ProofVersioned::V2(proof.clone()))
    }
    /// Verify a versioned service response against this frozen call, retained key and trusted SRS.
    /// This does not attach, sign or submit anything.
    pub fn verify_response(
        &self,
        params: &TrustedParameters,
        response: &[u8],
        max_response_bytes: usize,
    ) -> Result<()> {
        self.verified_response(params, response, max_response_bytes)
            .map(|_| ())
    }
    fn verified_response(
        &self,
        params: &TrustedParameters,
        response: &[u8],
        max_response_bytes: usize,
    ) -> Result<Proof> {
        if max_response_bytes == 0
            || max_response_bytes > MAX_RESPONSE
            || response.is_empty()
            || response.len() > max_response_bytes
        {
            return Err(Error::Limit);
        }
        self.validate_parameters(params)?;
        let versioned: ProofVersioned = decode(response).map_err(|_| Error::InvalidResponse)?;
        // The pinned /prove transport version is independent of ledger V3 attachment.
        let ProofVersioned::V2(proof) = versioned else {
            return Err(Error::InvalidResponse);
        };
        self.material
            .verifier
            .verify(&params.verifier, &proof, self.statement.iter().copied())
            .map_err(|_| Error::InvalidProof)?;
        Ok(proof)
    }
    /// Race proof construction against a host timer/cancellation future. Dropping this future
    /// drops the provider future. CPU-only native proving requires a host worker for hard stop.
    pub async fn prove<S: ProofService>(
        &self,
        service: &S,
        params: &TrustedParameters,
        max_response_bytes: usize,
        stop: impl Future<Output = Abort>,
    ) -> Result<ProvedIntent> {
        if max_response_bytes == 0 || max_response_bytes > MAX_RESPONSE {
            return Err(Error::Limit);
        }
        self.validate_parameters(params)?;
        let outcome = Rc::new(RefCell::new(None));
        let provider = CheckedProvider {
            prepared: self,
            service,
            params,
            max_response_bytes,
            outcome: outcome.clone(),
        };
        let work = self
            .intent
            .prove(
                0,
                provider,
                &self.material.parameters.cost_model.runtime_cost_model,
            )
            .fuse();
        let stop = stop.fuse();
        pin_mut!(work, stop);
        let result = select_biased! {
            reason = stop => return Err(match reason { Abort::Cancelled => Error::Cancelled, Abort::Deadline => Error::Deadline }),
            result = work => result,
        };
        let (_, intent) = result.map_err(|_| outcome.borrow().unwrap_or(Error::Attachment))?;
        let Some(ContractAction::Call(call)) = intent.actions.iter_deref().next() else {
            return Err(Error::Attachment);
        };
        if call
            .public_inputs(intent.binding_commitment.into())
            .map_err(|_| Error::Attachment)?
            != self.statement
        {
            return Err(Error::BindingMismatch);
        }
        let ProofVersioned::V3(proof) = &call.proof else {
            return Err(Error::Attachment);
        };
        self.material
            .verifier
            .verify(&params.verifier, proof, self.statement.iter().copied())
            .map_err(|_| Error::InvalidProof)?;
        let bytes = encode(&intent)?;
        let decoded: ProvedNativeIntent = decode(&bytes).map_err(|_| Error::Attachment)?;
        if encode(&decoded)? != bytes {
            return Err(Error::Attachment);
        }
        Ok(ProvedIntent {
            intent: decoded,
            bytes,
            contract_binding: self.contract_binding.clone(),
        })
    }
}

/// Native attached result only becomes available after local cryptographic verification.
/// The binding is frozen. Subsequent changes to bound call/intent fields require re-proving.
pub struct ProvedIntent {
    intent: ProvedNativeIntent,
    bytes: Vec<u8>,
    contract_binding: Option<ContractStateBinding>,
}
impl ProvedIntent {
    pub fn native(&self) -> &ProvedNativeIntent {
        &self.intent
    }
    pub fn serialized(&self) -> &[u8] {
        &self.bytes
    }
    pub(crate) fn contract_binding(&self) -> Option<&ContractStateBinding> {
        self.contract_binding.as_ref()
    }
    /// Public proof result. The private unsealed binding randomness is replaced by its commitment.
    /// This projection supplies neither funding nor the sealed transaction binding proof.
    pub fn public_serialized(&self) -> Result<Vec<u8>> {
        let intent: PublicProvedNativeIntent = Intent {
            guaranteed_unshielded_offer: self.intent.guaranteed_unshielded_offer.clone(),
            fallible_unshielded_offer: self.intent.fallible_unshielded_offer.clone(),
            actions: self.intent.actions.clone(),
            dust_actions: self.intent.dust_actions.clone(),
            ttl: self.intent.ttl,
            binding_commitment: self.intent.binding_commitment.into(),
        };
        let bytes = encode(&intent)?;
        let decoded: PublicProvedNativeIntent = decode(&bytes)?;
        if encode(&decoded)? != bytes {
            return Err(Error::Attachment);
        }
        Ok(bytes)
    }
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Abort {
    Cancelled,
    Deadline,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct ServiceError;
impl fmt::Display for ServiceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("nightlean_proof_service_failure")
    }
}
impl std::error::Error for ServiceError {}

/// Explicit private-data disclosure to a host-authorized proof service.
/// No ambient network/filesystem behavior lives in this trait or in the core.
#[allow(async_fn_in_trait)]
pub trait ProofService {
    async fn prove(&self, request: ProofRequest<'_>) -> std::result::Result<Vec<u8>, ServiceError>;
}
/// Private request, intentionally lacks Debug. A remote adapter must obtain host authority
/// before transmitting this witness-bearing material and enforce limits while reading bytes.
pub struct ProofRequest<'a> {
    preimage: &'a ProofPreimage,
    material: &'a ProvingKeyMaterial,
    prover: &'a ProverKey<IrSource>,
    pub parameters: &'a TrustedParameters,
    pub max_response_bytes: usize,
    expected_statement: &'a [Fr],
    expected_activity: &'a [Option<usize>],
}
impl ProofRequest<'_> {
    /// Official /prove wire payload: (versioned preimage, retained keys+IR, no binding override).
    /// Binding is already replaced by the upstream native intent prover's exact value.
    pub fn private_wire_payload(&self) -> Result<zeroize::Zeroizing<Vec<u8>>> {
        encode(&(
            ProofPreimageVersioned::V2(std::sync::Arc::new(self.preimage.clone())),
            Some(self.material.clone()),
            Option::<Fr>::None,
        ))
        .map(zeroize::Zeroizing::new)
    }
    /// Run the selected pinned native prover with host-supplied entropy and parameters.
    pub async fn prove_locally(
        self,
        rng: impl Rng + CryptoRng,
    ) -> std::result::Result<Vec<u8>, ServiceError> {
        let ir = IrSource::load(&self.material.ir_source[..]).map_err(|_| ServiceError)?;
        let (proof, statement, activity) = ir
            .prove(rng, self.parameters, self.prover.clone(), self.preimage)
            .await
            .map_err(|_| ServiceError)?;
        if statement != self.expected_statement || activity != self.expected_activity {
            return Err(ServiceError);
        }
        let response = encode(&ProofVersioned::V2(proof)).map_err(|_| ServiceError)?;
        if response.len() > self.max_response_bytes {
            return Err(ServiceError);
        }
        Ok(response)
    }
}
/// One-use local prover. The host supplies fresh entropy for every attempt.
pub struct LocalProver<R>(RefCell<Option<R>>);
impl<R: Rng + CryptoRng> LocalProver<R> {
    pub fn new(rng: R) -> Self {
        Self(RefCell::new(Some(rng)))
    }
}
impl<R: Rng + CryptoRng> ProofService for LocalProver<R> {
    async fn prove(&self, request: ProofRequest<'_>) -> std::result::Result<Vec<u8>, ServiceError> {
        let rng = self.0.borrow_mut().take().ok_or(ServiceError)?;
        request.prove_locally(rng).await
    }
}
struct CheckedProvider<'a, S> {
    prepared: &'a PreparedProof,
    service: &'a S,
    params: &'a TrustedParameters,
    max_response_bytes: usize,
    outcome: Rc<RefCell<Option<Error>>>,
}
impl<S> Clone for CheckedProvider<'_, S> {
    fn clone(&self) -> Self {
        Self {
            prepared: self.prepared,
            service: self.service,
            params: self.params,
            max_response_bytes: self.max_response_bytes,
            outcome: self.outcome.clone(),
        }
    }
}
impl<S> Resolver for CheckedProvider<'_, S> {
    async fn resolve_key(&self, key: KeyLocation) -> io::Result<Option<ProvingKeyMaterial>> {
        if key.0.as_ref() != self.prepared.material.entrypoint {
            return Err(io::Error::other("nightlean_proof_unknown_key"));
        }
        Ok(Some(self.prepared.material.native.clone()))
    }
}
impl<S: ProofService> ProvingProvider for CheckedProvider<'_, S> {
    async fn check(&self, preimage: &ProofPreimage) -> anyhow::Result<Vec<Option<usize>>> {
        let result = preimage
            .check(&self.prepared.material.circuit)
            .map_err(|_| Error::InvalidIntent);
        match result {
            Ok(activity) if activity == self.prepared.activity => Ok(activity),
            _ => {
                *self.outcome.borrow_mut() = Some(Error::InvalidIntent);
                Err(Error::InvalidIntent.into())
            }
        }
    }
    async fn prove(self, preimage: &ProofPreimage, overwrite: Option<Fr>) -> anyhow::Result<Proof> {
        let result = self.checked_prove(preimage, overwrite).await;
        if let Err(error) = &result {
            *self.outcome.borrow_mut() = Some(*error);
        }
        result.map_err(Into::into)
    }
    fn split(&mut self) -> Self {
        self.clone()
    }
    fn resolver(&self) -> &impl Resolver {
        self
    }
}
impl<S: ProofService> CheckedProvider<'_, S> {
    async fn checked_prove(
        &self,
        preimage: &ProofPreimage,
        overwrite: Option<Fr>,
    ) -> Result<Proof> {
        if overwrite != self.prepared.statement.first().copied() {
            return Err(Error::BindingMismatch);
        }
        let mut preimage = preimage.clone();
        preimage.binding_input = overwrite.ok_or(Error::BindingMismatch)?;
        let response = self
            .service
            .prove(ProofRequest {
                preimage: &preimage,
                material: &self.prepared.material.native,
                prover: &self.prepared.material.prover,
                parameters: self.params,
                max_response_bytes: self.max_response_bytes,
                expected_statement: &self.prepared.statement,
                expected_activity: &self.prepared.activity,
            })
            .await
            .map_err(|_| Error::Service)?;
        self.prepared
            .verified_response(self.params, &response, self.max_response_bytes)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use futures::{executor::block_on, future::pending};
    use rand::rngs::OsRng;

    #[cfg(feature = "zkir-321")]
    fn issue43_fixture(name: &str) -> String {
        std::env::var(format!("NIGHTLEAN_ISSUE43_{name}"))
            .unwrap_or_else(|_| panic!("missing NIGHTLEAN_ISSUE43_{name}"))
    }

    fn issue43_empty_activity_fixture(name: &str) -> String {
        std::env::var(format!("NIGHTLEAN_ISSUE43_EMPTY_{name}"))
            .unwrap_or_else(|_| panic!("missing NIGHTLEAN_ISSUE43_EMPTY_{name}"))
    }

    #[test]
    fn contract_state_binding_rejects_wrong_operation_and_successor() {
        let state = ContractState::<Db>::default();
        let expected = encode(&state).unwrap();
        let binding = ContractStateBinding {
            contract_set_identity: "11".repeat(32),
            deployment_identity: "22".repeat(32),
            state_schema_sha256: "33".repeat(32),
            address: "44".repeat(32),
            operation: "apply".into(),
            context_identity: "55".repeat(32),
            current_state_sha256: Some(hex::encode(Sha256::digest(&expected))),
            current_state: Some(expected.clone()),
            expected_state: expected.clone(),
            deployment: false,
        };
        assert!(binding.matches_target("44".repeat(32).as_str(), "apply"));
        assert!(!binding.matches_target("44".repeat(32).as_str(), "claim"));
        let token = binding
            .admit_committed_state(&expected, &expected, &"aa".repeat(32), false)
            .unwrap();
        assert_eq!(token.state_bytes, expected);
        let mut wrong_successor = expected.clone();
        wrong_successor.push(0);
        assert!(
            binding
                .admit_committed_state(&wrong_successor, &wrong_successor, &"aa".repeat(32), false,)
                .is_err()
        );
    }

    #[cfg(feature = "zkir-321")]
    #[test]
    #[ignore = "requires authenticated conditional-write bundle, private config and trusted SRS"]
    fn inactive_guarded_write_matches_native_noop_preview_and_binds_skipped_fields() {
        let bundle_dir = issue43_fixture("BUNDLE");
        let manifest_digest = issue43_fixture("MANIFEST_SHA256");
        let bundle =
            crate::artifacts::verify(std::path::Path::new(&bundle_dir), Some(&manifest_digest))
                .unwrap();
        let config_bytes = std::fs::read(issue43_fixture("PRIVATE_CONFIG")).unwrap();
        let parameters_bytes = std::fs::read(issue43_fixture("PROOF_PARAMETERS")).unwrap();
        let parameters_digest = issue43_fixture("PROOF_PARAMETERS_SHA256");
        let ttl = 2_000_000_000;
        let mut prepared =
            PreparedProof::from_config(&bundle, &config_bytes, ttl, &mut OsRng).unwrap();
        let parameters =
            TrustedParameters::from_bytes(&parameters_bytes, prepared.k(), &parameters_digest)
                .unwrap();
        assert_eq!(
            prepared.activity,
            [
                None,
                None,
                Some(5),
                Some(5),
                Some(1),
                Some(4),
                Some(5),
                Some(5),
                Some(1),
            ]
        );
        let ContractAction::Call(source_call) =
            prepared.intent.actions.iter_deref().next().unwrap()
        else {
            unreachable!()
        };
        let preview = preview_call_activity(
            source_call,
            &prepared.activity,
            prepared.intent.binding_commitment.into(),
            &prepared.material.parameters.cost_model.runtime_cost_model,
        )
        .unwrap();
        assert_eq!(preview.statement, prepared.statement);

        let proved = block_on(prepared.prove(
            &LocalProver::new(OsRng),
            &parameters,
            MAX_RESPONSE,
            pending(),
        ))
        .unwrap();
        let ContractAction::Call(actual) = proved.native().actions.iter_deref().next().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(
            actual.guaranteed_transcript,
            preview.call.guaranteed_transcript
        );
        assert_eq!(actual.fallible_transcript, preview.call.fallible_transcript);
        assert_eq!(
            actual
                .public_inputs(proved.native().binding_commitment.into())
                .unwrap(),
            prepared.statement
        );
        let noop_fields = actual
            .guaranteed_transcript
            .iter()
            .chain(actual.fallible_transcript.iter())
            .flat_map(|transcript| transcript.program.iter_deref())
            .filter_map(|op| match op {
                onchain_runtime::ops::Op::Noop { n } => Some(*n),
                _ => None,
            })
            .try_fold(0u32, u32::checked_add)
            .unwrap();
        assert_eq!(noop_fields, 26);

        let ContractAction::Call(call) = proved.native().actions.iter_deref().next().unwrap()
        else {
            unreachable!()
        };
        let ProofVersioned::V3(proof) = &call.proof else {
            unreachable!()
        };
        let response = encode(&ProofVersioned::V2(proof.clone())).unwrap();
        assert_eq!(
            prepared.verify_response(&parameters, &response, MAX_RESPONSE),
            Ok(())
        );
        let skipped_field = prepared
            .statement
            .iter()
            .enumerate()
            .skip(2)
            .find_map(|(index, field)| (*field == Fr::from(0u64)).then_some(index))
            .expect("skipped Noop fields are public zero elements");
        prepared.statement[skipped_field] = Fr::from(1u64);
        assert_eq!(
            prepared.verify_response(&parameters, &response, MAX_RESPONSE),
            Err(Error::InvalidProof)
        );

        let bundle_dir = issue43_empty_activity_fixture("BUNDLE");
        let manifest_digest = issue43_empty_activity_fixture("MANIFEST_SHA256");
        let bundle =
            crate::artifacts::verify(std::path::Path::new(&bundle_dir), Some(&manifest_digest))
                .unwrap();
        let config_bytes = std::fs::read(issue43_empty_activity_fixture("PRIVATE_CONFIG")).unwrap();
        let parameters_bytes =
            std::fs::read(issue43_empty_activity_fixture("PROOF_PARAMETERS")).unwrap();
        let parameters_digest = issue43_empty_activity_fixture("PROOF_PARAMETERS_SHA256");
        let empty_prepared =
            PreparedProof::from_config(&bundle, &config_bytes, ttl, &mut OsRng).unwrap();
        assert!(empty_prepared.activity.iter().all(Option::is_some));
        assert_eq!(empty_prepared.activity.iter().flatten().sum::<usize>(), 26);
        let ContractAction::Call(empty_source_call) =
            empty_prepared.intent.actions.iter_deref().next().unwrap()
        else {
            unreachable!()
        };
        let empty_source_transcript = empty_source_call
            .guaranteed_transcript
            .as_ref()
            .expect("all-inactive source retains an empty transcript container");
        assert_eq!(empty_source_transcript.program.len(), 0);
        assert!(empty_source_call.fallible_transcript.is_none());
        let empty_preview = preview_call_activity(
            empty_source_call,
            &empty_prepared.activity,
            empty_prepared.intent.binding_commitment.into(),
            &empty_prepared
                .material
                .parameters
                .cost_model
                .runtime_cost_model,
        )
        .unwrap();
        assert_eq!(empty_preview.statement, empty_prepared.statement);
        let empty_parameters = TrustedParameters::from_bytes(
            &parameters_bytes,
            empty_prepared.k(),
            &parameters_digest,
        )
        .unwrap();
        let empty_proved = block_on(empty_prepared.prove(
            &LocalProver::new(OsRng),
            &empty_parameters,
            MAX_RESPONSE,
            pending(),
        ))
        .unwrap();
        let ContractAction::Call(empty_actual) =
            empty_proved.native().actions.iter_deref().next().unwrap()
        else {
            unreachable!()
        };
        assert_eq!(
            empty_actual.guaranteed_transcript,
            empty_preview.call.guaranteed_transcript
        );
        assert_eq!(
            empty_actual.fallible_transcript,
            empty_preview.call.fallible_transcript
        );
        assert_eq!(
            empty_actual
                .public_inputs(empty_proved.native().binding_commitment.into())
                .unwrap(),
            empty_prepared.statement
        );
        let empty_noop_fields = empty_actual
            .guaranteed_transcript
            .iter()
            .chain(empty_actual.fallible_transcript.iter())
            .flat_map(|transcript| transcript.program.iter_deref())
            .filter_map(|op| match op {
                onchain_runtime::ops::Op::Noop { n } => Some(*n),
                _ => None,
            })
            .try_fold(0u32, u32::checked_add)
            .unwrap();
        assert_eq!(empty_noop_fields, 26);
        assert_eq!(
            empty_actual
                .guaranteed_transcript
                .as_ref()
                .unwrap()
                .program
                .iter_deref()
                .filter(|op| !matches!(op, onchain_runtime::ops::Op::Noop { .. }))
                .count(),
            0
        );
    }

    #[test]
    #[ignore = "requires authenticated real source bundle, private inputs, SRS and another retained VK"]
    fn real_crypto_rejects_each_statement_field_and_wrong_key() {
        let root = std::env::var("NIGHTLEAN_TEST_BUNDLE").unwrap();
        let digest = std::env::var("NIGHTLEAN_TEST_MANIFEST_SHA256").unwrap();
        let config =
            std::fs::read(std::env::var("NIGHTLEAN_TEST_PRIVATE_CONFIG").unwrap()).unwrap();
        let parameters =
            std::fs::read(std::env::var("NIGHTLEAN_TEST_PROOF_PARAMETERS").unwrap()).unwrap();
        let parameter_digest = std::env::var("NIGHTLEAN_TEST_PROOF_PARAMETERS_SHA256").unwrap();
        let bundle = crate::artifacts::verify(root.as_ref(), Some(&digest)).unwrap();
        let mut prepared =
            PreparedProof::from_config(&bundle, &config, 2_000_000_000, &mut OsRng).unwrap();
        let params =
            TrustedParameters::from_bytes(&parameters, prepared.k(), &parameter_digest).unwrap();
        let proved =
            block_on(prepared.prove(&LocalProver::new(OsRng), &params, MAX_RESPONSE, pending()))
                .unwrap();
        let ContractAction::Call(call) = proved.native().actions.iter_deref().next().unwrap()
        else {
            unreachable!()
        };
        let ProofVersioned::V3(proof) = &call.proof else {
            unreachable!()
        };
        let response = encode(&ProofVersioned::V2(proof.clone())).unwrap();
        prepared
            .verify_response(&params, &response, MAX_RESPONSE)
            .unwrap();
        // Binding, communication commitment and every public statement field receive independent tests.
        for index in 0..prepared.statement.len() {
            let old = prepared.statement[index];
            prepared.statement[index] = old + Fr::from(1u64);
            assert_eq!(
                prepared.verify_response(&params, &response, MAX_RESPONSE),
                Err(Error::InvalidProof),
                "statement index {index}"
            );
            prepared.statement[index] = old;
        }
        let other = std::fs::read(std::env::var("NIGHTLEAN_TEST_OTHER_VERIFIER").unwrap()).unwrap();
        let other: VerifierKey = decode(&other).unwrap();
        other.init().unwrap();
        prepared.material.verifier = other;
        assert_eq!(
            prepared.verify_response(&params, &response, MAX_RESPONSE),
            Err(Error::InvalidProof)
        );
    }
}
