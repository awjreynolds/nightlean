//! Native proof service boundary. Public artifacts stay retained, private values have no Debug.
//! This API proves a frozen single-call intent. It does not fund, sign, or submit transactions.
use crate::{
    Db, Plan,
    artifacts::{Role, VerifiedBundle},
    assembly::NativeIntent,
    zkir::IrSource,
};
use futures::{Future, FutureExt, pin_mut, select_biased};
use ledger::structure::{
    ContractAction, Intent, LedgerParameters, ProofMarker, ProofPreimageVersioned, ProofVersioned,
    Signature,
};
use midnight_proofs::{plonk::ConstraintSystem, poly::kzg::params::ParamsKZG, utils::SerdeFormat};
use midnight_zk_stdlib::{MidnightPK, Relation, ZkStdLib, ZkStdLibArch};
use rand::{CryptoRng, Rng};
use serialize::{Deserializable, Serializable, Tagged, tagged_deserialize, tagged_serialize};
use sha2::{Digest, Sha256};
use std::{cell::RefCell, fmt, io, rc::Rc, sync::Arc};
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
    let len = u32::deserialize(&mut reader, 0).map_err(|_| Error::InvalidArtifacts)? as usize;
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
        let op_count = call
            .guaranteed_transcript
            .iter()
            .chain(call.fallible_transcript.iter())
            .map(|t| t.program.len())
            .sum::<usize>();
        if activity.len() != op_count || activity.iter().any(Option::is_some) {
            return Err(Error::UnsupportedActivity);
        }
        let statement = call
            .public_inputs(intent.binding_commitment.into())
            .map_err(|_| Error::InvalidIntent)?;
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
        Ok(())
    }
    pub fn deployment_intent(&self) -> Option<&NativeIntent> {
        self.deployment.as_ref()
    }
    pub fn k(&self) -> u8 {
        self.material.circuit.k()
    }
    pub fn profile(&self) -> &'static str {
        crate::profile::NAME
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
        if params.k != self.k() {
            return Err(Error::InvalidParameters);
        }
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
        if params.k != self.k() {
            return Err(Error::InvalidParameters);
        }
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
        if params.k != self.k() {
            return Err(Error::InvalidParameters);
        }
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
        })
    }
}

/// Native attached result only becomes available after local cryptographic verification.
/// The binding is frozen. Subsequent changes to bound call/intent fields require re-proving.
pub struct ProvedIntent {
    intent: ProvedNativeIntent,
    bytes: Vec<u8>,
}
impl ProvedIntent {
    pub fn native(&self) -> &ProvedNativeIntent {
        &self.intent
    }
    pub fn serialized(&self) -> &[u8] {
        &self.bytes
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
        if statement != self.expected_statement || activity.iter().any(Option::is_some) {
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
