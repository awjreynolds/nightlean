//! Native proof ABI phase A plus explicit owned client tasks for phase B.
//! No foreign callback, stack frame or borrowed buffer survives an ABI call.
use crate::{
    artifacts,
    assembly::{CheckedNativeCall, CompositionOffer},
    proof::{CompositionDraft, CompositionMaterial, PreparedProof, TrustedParameters},
};
use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use futures::executor::block_on;
use ledger::structure::LedgerState;
use onchain_runtime::{
    context::QueryContext,
    state::{ContractState, EntryPointBuf},
};
use rand::{Rng, SeedableRng, rngs::StdRng};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use serialize::{Deserializable, Serializable, Tagged, tagged_deserialize, tagged_serialize};
#[cfg(feature = "localnet")]
use std::time::Duration;
use std::{
    collections::BTreeMap,
    panic::{AssertUnwindSafe, catch_unwind},
    path::PathBuf,
    sync::{Arc, Mutex, OnceLock},
};
use storage::arena::Sp;
use transient_crypto::{
    curve::Fr,
    proofs::{VerifierKey, Zkir},
};
use zeroize::{Zeroize, Zeroizing};

pub const OK: i32 = 0;
pub const INVALID_ARGUMENT: i32 = 1;
pub const INVALID_HANDLE: i32 = 2;
pub const INVALID_STATE: i32 = 3;
pub const INVALID_RESPONSE: i32 = 4;
pub const LIMIT: i32 = 5;
pub const INTERNAL: i32 = 6;
pub const BUFFER_TOO_SMALL: i32 = 7;
// Real retained claim: 456,374 private request bytes, 3,852 response bytes, 4,433 attached bytes.
pub const MAX_BYTES: usize = 1_048_576;
const MAX_DESCRIPTOR: usize = 65_536;
const MAX_PARAMETERS: usize = 134_217_728;
const MAX_BUNDLE: u64 = 16 * 1024 * 1024;
const MAX_RECOVERY_CONTEXT: usize = 1_200_000;
const MAX_SESSIONS: usize = 8;
const MAX_RESULTS: usize = 64;
const MAX_PRIVATE: usize = 16;
const MAX_WORK: usize = 2;
const OPERATION: &str = "native.prove.v1";

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Begin {
    abi_version: u32,
    profile: String,
    bundle_directory: PathBuf,
    trusted_manifest_sha256: String,
    proof_parameters_sha256: String,
    k: u8,
    ttl: u64,
    proof_service_capability: String,
    max_response_bytes: usize,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct WitnessTargetBegin {
    abi_version: u32,
    profile: String,
    bundle_directory: PathBuf,
    trusted_manifest_sha256: String,
    proof_parameters_sha256: String,
    k: u8,
    ttl: u64,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct WitnessProofBegin {
    abi_version: u32,
    profile: String,
    trusted_manifest_sha256: String,
    proof_parameters_sha256: String,
    k: u8,
    ttl: u64,
    proof_service_capability: String,
    max_response_bytes: usize,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct CompositionOwnerBegin {
    abi_version: u32,
    profile: String,
    bundle_directory: PathBuf,
    trusted_manifest_sha256: String,
    proof_parameters_sha256: String,
    k: u8,
    ttl: u64,
    network_id: String,
    contract_address: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ContractBundleBegin {
    bundle_directory: PathBuf,
    trusted_manifest_sha256: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ContractTargetBegin {
    abi_version: u32,
    profile: String,
    ttl: u64,
    journal_directory: PathBuf,
    operations: Vec<ContractBundleBegin>,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ContractCallBegin {
    abi_version: u32,
    operation: String,
    k: u8,
    ttl: u64,
    proof_parameters_sha256: String,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Reply {
    abi_version: u32,
    request_id: u64,
    operation: String,
    capability: String,
    profile: String,
}
enum Phase {
    Pending,
    Complete(Vec<u8>),
    Cancelled,
}
struct Session {
    prepared: Option<Arc<PreparedProof>>,
    parameters: Option<Arc<TrustedParameters>>,
    payload: Zeroizing<Vec<u8>>,
    request_id: u64,
    capability: String,
    manifest: String,
    max_response: usize,
    phase: Phase,
    local_started: bool,
    proved: Option<crate::proof::ProvedIntent>,
    deployment: Option<crate::proof::ProvedNativeIntent>,
    client_started: [bool; 2],
    source_runtime: Option<crate::host::Runtime>,
    witness_context: Option<u64>,
}
struct TargetContext {
    bundle_directory: PathBuf,
    target: Arc<crate::proof::WitnessTarget>,
    reservation: Option<ProofReservation>,
}
struct CompositionOwner {
    bundle: artifacts::VerifiedBundle,
    parameters: TrustedParameters,
    entry_point: EntryPointBuf,
    circuit: crate::zkir::IrSource,
    execution: crate::Execution,
    snapshot: LedgerState<crate::Db>,
    address: ContractAddress,
    communication_commitment_rand: Fr,
    ttl: u64,
    proved: bool,
}
struct CompositionOwnerSlot {
    owner: Arc<Mutex<CompositionOwner>>,
    busy: bool,
}
struct ContractTargetSlot {
    target: Arc<crate::proof::WitnessContractTarget>,
    #[cfg(feature = "localnet")]
    journal_directory: PathBuf,
    busy: bool,
    deployment_started: bool,
}
struct ContractStateSlot {
    current: Option<crate::proof::CurrentStateContext>,
    busy: bool,
}
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct ProofReservation {
    session: u64,
    request_id: u64,
}
struct Private {
    bytes: Zeroizing<Vec<u8>>,
    owner: u64,
}
struct Registry {
    next: u64,
    sessions: BTreeMap<u64, Session>,
    targets: BTreeMap<u64, TargetContext>,
    composition_owners: BTreeMap<u64, CompositionOwnerSlot>,
    contract_targets: BTreeMap<u64, ContractTargetSlot>,
    contract_states: BTreeMap<u64, ContractStateSlot>,
    contract_client_targets: BTreeMap<u64, Arc<crate::proof::WitnessContractTarget>>,
    results: BTreeMap<u64, Vec<u8>>,
    private: BTreeMap<u64, Private>,
    active_work: usize,
    clients: BTreeMap<u64, Option<crate::native_client::Driver>>,
    requests: BTreeMap<u64, ServiceRequest>,
    replies: BTreeMap<u64, ServiceResponse>,
}
impl Default for Registry {
    fn default() -> Self {
        Self {
            next: 1 << 62,
            sessions: BTreeMap::new(),
            targets: BTreeMap::new(),
            composition_owners: BTreeMap::new(),
            contract_targets: BTreeMap::new(),
            contract_states: BTreeMap::new(),
            contract_client_targets: BTreeMap::new(),
            results: BTreeMap::new(),
            private: BTreeMap::new(),
            active_work: 0,
            clients: BTreeMap::new(),
            requests: BTreeMap::new(),
            replies: BTreeMap::new(),
        }
    }
}
static REGISTRY: OnceLock<Mutex<Registry>> = OnceLock::new();
fn registry<T>(f: impl FnOnce(&mut Registry) -> Result<T, i32>) -> Result<T, i32> {
    let mut r = REGISTRY
        .get_or_init(|| Mutex::new(Registry::default()))
        .lock()
        .map_err(|_| INTERNAL)?;
    f(&mut r)
}
impl Registry {
    fn token(&mut self) -> Result<u64, i32> {
        self.next = self
            .next
            .checked_add(1)
            .filter(|n| *n < 1 << 63)
            .ok_or(LIMIT)?;
        Ok(self.next)
    }
    fn result(&mut self, bytes: Vec<u8>) -> Result<u64, i32> {
        if bytes.len() > MAX_BYTES || self.results.len() >= MAX_RESULTS {
            return Err(LIMIT);
        }
        let token = self.token()?;
        self.results.insert(token, bytes);
        Ok(token)
    }
    fn revoke_private(&mut self, owner: u64) {
        self.private.retain(|_, p| p.owner != owner);
    }
    fn live_contexts(&self) -> usize {
        self.sessions.len()
            + self.clients.len()
            + self.targets.len()
            + self.composition_owners.len()
            + self.contract_targets.len()
            + self.contract_states.len()
    }
}
// Work outlives cancellation of its session. Its resource slot ends only when the call returns.
pub(crate) struct Work;
impl Work {
    pub(crate) fn reserve() -> Result<Self, i32> {
        registry(|r| {
            if r.active_work >= MAX_WORK {
                return Err(LIMIT);
            }
            r.active_work += 1;
            Ok(Self)
        })
    }
}
impl Drop for Work {
    fn drop(&mut self) {
        let _ = registry(|r| {
            r.active_work -= 1;
            Ok(())
        });
    }
}
pub(crate) fn guard(f: impl FnOnce() -> Result<(), i32>) -> i32 {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(Ok(())) => OK,
        Ok(Err(code)) => code,
        Err(_) => INTERNAL,
    }
}
pub(crate) unsafe fn output(pointer: *mut u64) -> Result<(), i32> {
    if pointer.is_null() {
        return Err(INVALID_ARGUMENT);
    }
    unsafe {
        pointer.write(0);
    }
    Ok(())
}
pub(crate) unsafe fn input<'a>(
    pointer: *const u8,
    length: usize,
    max: usize,
) -> Result<&'a [u8], i32> {
    if pointer.is_null() || length == 0 {
        return Err(INVALID_ARGUMENT);
    }
    if length > max || length > isize::MAX as usize {
        return Err(LIMIT);
    }
    Ok(unsafe { std::slice::from_raw_parts(pointer, length) })
}
pub(crate) unsafe fn entropy(pointer: *const u8, length: usize) -> Result<StdRng, i32> {
    if length != 32 {
        return Err(INVALID_ARGUMENT);
    }
    let bytes = unsafe { input(pointer, length, 32)? };
    let mut seed = [0u8; 32];
    seed.copy_from_slice(bytes);
    let rng = StdRng::from_seed(seed);
    seed.zeroize();
    Ok(rng)
}
fn encoded(value: serde_json::Value) -> Result<Vec<u8>, i32> {
    serde_json::to_vec(&value).map_err(|_| INTERNAL)
}
fn pending(session: &Session) -> Result<(), i32> {
    if matches!(session.phase, Phase::Pending) {
        Ok(())
    } else {
        Err(INVALID_STATE)
    }
}

fn decode_tagged<T>(bytes: &[u8]) -> Result<T, i32>
where
    T: Deserializable + Serializable + Tagged,
{
    let mut reader = bytes;
    let decoded = tagged_deserialize(&mut reader).map_err(|_| INVALID_ARGUMENT)?;
    if !reader.is_empty() {
        return Err(INVALID_ARGUMENT);
    }
    let mut encoded = Vec::new();
    tagged_serialize(&decoded, &mut encoded).map_err(|_| INVALID_ARGUMENT)?;
    if encoded != bytes {
        return Err(INVALID_ARGUMENT);
    }
    Ok(decoded)
}

struct CompositionOwnerReservation(u64);
impl CompositionOwnerReservation {
    fn reserve(token: u64) -> Result<(Self, Arc<Mutex<CompositionOwner>>), i32> {
        let owner = registry(|r| {
            let slot = r.composition_owners.get_mut(&token).ok_or(INVALID_HANDLE)?;
            if slot.busy {
                return Err(INVALID_STATE);
            }
            slot.busy = true;
            Ok(Arc::clone(&slot.owner))
        })?;
        Ok((Self(token), owner))
    }
}
impl Drop for CompositionOwnerReservation {
    fn drop(&mut self) {
        let _ = registry(|r| {
            let slot = r.composition_owners.get_mut(&self.0).ok_or(INTERNAL)?;
            slot.busy = false;
            Ok(())
        });
    }
}

struct ContractTargetReservation {
    token: u64,
    target: Arc<crate::proof::WitnessContractTarget>,
    #[cfg(feature = "localnet")]
    journal_directory: PathBuf,
    deployment_started: bool,
}
impl ContractTargetReservation {
    fn reserve(token: u64) -> Result<Self, i32> {
        registry(|r| {
            let slot = r.contract_targets.get_mut(&token).ok_or(INVALID_HANDLE)?;
            if slot.busy {
                return Err(INVALID_STATE);
            }
            slot.busy = true;
            Ok(Self {
                token,
                target: Arc::clone(&slot.target),
                #[cfg(feature = "localnet")]
                journal_directory: slot.journal_directory.clone(),
                deployment_started: slot.deployment_started,
            })
        })
    }
}
impl Drop for ContractTargetReservation {
    fn drop(&mut self) {
        let _ = registry(|r| {
            let slot = r.contract_targets.get_mut(&self.token).ok_or(INTERNAL)?;
            slot.busy = false;
            Ok(())
        });
    }
}

struct ContractStateReservation {
    token: u64,
    current: Option<crate::proof::CurrentStateContext>,
}
impl ContractStateReservation {
    fn reserve(token: u64) -> Result<Self, i32> {
        registry(|r| {
            let slot = r.contract_states.get_mut(&token).ok_or(INVALID_HANDLE)?;
            if slot.busy {
                return Err(INVALID_STATE);
            }
            let current = slot.current.take().ok_or(INVALID_STATE)?;
            slot.busy = true;
            Ok(Self {
                token,
                current: Some(current),
            })
        })
    }

    fn current(&self) -> Result<&crate::proof::CurrentStateContext, i32> {
        self.current.as_ref().ok_or(INVALID_STATE)
    }

    fn consume(&mut self) {
        self.current.take();
    }
}
impl Drop for ContractStateReservation {
    fn drop(&mut self) {
        let current = self.current.take();
        let _ = registry(|r| {
            if let Some(current) = current {
                let slot = r.contract_states.get_mut(&self.token).ok_or(INTERNAL)?;
                slot.current = Some(current);
                slot.busy = false;
            } else {
                r.contract_states.remove(&self.token).ok_or(INTERNAL)?;
            }
            Ok(())
        });
    }
}

struct ContractStateRegistration {
    token: u64,
    committed: bool,
}
impl ContractStateRegistration {
    fn reserve() -> Result<Self, i32> {
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                return Err(LIMIT);
            }
            let token = r.token()?;
            r.contract_states.insert(
                token,
                ContractStateSlot {
                    current: None,
                    busy: true,
                },
            );
            Ok(Self {
                token,
                committed: false,
            })
        })
    }

    fn commit(mut self, current: crate::proof::CurrentStateContext) -> Result<u64, i32> {
        registry(|r| {
            let slot = r.contract_states.get_mut(&self.token).ok_or(INTERNAL)?;
            if !slot.busy || slot.current.is_some() {
                return Err(INTERNAL);
            }
            slot.current = Some(current);
            slot.busy = false;
            Ok(())
        })?;
        self.committed = true;
        Ok(self.token)
    }
}
impl Drop for ContractStateRegistration {
    fn drop(&mut self) {
        if !self.committed {
            let _ = registry(|r| {
                r.contract_states.remove(&self.token).ok_or(INTERNAL)?;
                Ok(())
            });
        }
    }
}

struct ContractClientRegistration {
    token: u64,
    committed: bool,
}
impl ContractClientRegistration {
    fn reserve() -> Result<Self, i32> {
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                return Err(LIMIT);
            }
            let token = r.token()?;
            r.clients.insert(token, None);
            Ok(Self {
                token,
                committed: false,
            })
        })
    }

    fn commit(
        mut self,
        driver: crate::native_client::Driver,
        target_token: u64,
        target: Arc<crate::proof::WitnessContractTarget>,
        deployment_start: bool,
    ) -> Result<u64, i32> {
        registry(|r| {
            if !r.clients.contains_key(&self.token) {
                return Err(INTERNAL);
            }
            if deployment_start {
                let slot = r
                    .contract_targets
                    .get(&target_token)
                    .ok_or(INVALID_HANDLE)?;
                if !slot.busy || slot.deployment_started {
                    return Err(INVALID_STATE);
                }
            }
            *r.clients.get_mut(&self.token).ok_or(INTERNAL)? = Some(driver);
            r.contract_client_targets.insert(self.token, target);
            if deployment_start {
                r.contract_targets
                    .get_mut(&target_token)
                    .ok_or(INTERNAL)?
                    .deployment_started = true;
            }
            Ok(())
        })?;
        self.committed = true;
        Ok(self.token)
    }
}
impl Drop for ContractClientRegistration {
    fn drop(&mut self) {
        if !self.committed {
            let _ = registry(|r| {
                r.clients.remove(&self.token).ok_or(INTERNAL)?;
                Ok(())
            });
        }
    }
}

struct NativePrivateInputs(BTreeMap<String, Json>);
impl Drop for NativePrivateInputs {
    fn drop(&mut self) {
        for value in self.0.values_mut() {
            crate::control::wipe_json(value);
        }
    }
}

/// # Safety
/// Every input pointer must reference immutable bytes until return. The state and
/// parameter snapshots come from the host's authenticated chain observation.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_composition_owner_begin(
    descriptor: *const u8,
    descriptor_len: usize,
    inputs: *const u8,
    inputs_len: usize,
    contract_state: *const u8,
    contract_state_len: usize,
    ledger_parameters: *const u8,
    ledger_parameters_len: usize,
    proof_parameters: *const u8,
    proof_parameters_len: usize,
    coins: *const u8,
    coins_len: usize,
    out_owner: *mut u64,
    out_offer: *mut u64,
) -> i32 {
    guard(|| {
        unsafe {
            output(out_owner)?;
            output(out_offer)?;
        }
        let begin: CompositionOwnerBegin =
            serde_json::from_slice(unsafe { input(descriptor, descriptor_len, MAX_DESCRIPTOR)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        if begin.abi_version != 1
            || begin.profile != crate::profile::NAME
            || begin.bundle_directory.as_os_str().len() > 4096
            || begin.ttl == 0
            || begin.network_id.is_empty()
            || begin.network_id.len() > 128
            || begin.contract_address.len() != 64
            || !begin
                .contract_address
                .bytes()
                .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b))
            || !(1..=20).contains(&begin.k)
        {
            return Err(INVALID_ARGUMENT);
        }
        let _work = Work::reserve()?;
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                Err(LIMIT)
            } else {
                Ok(())
            }
        })?;

        let bundle = artifacts::verify_with_limit(
            &begin.bundle_directory,
            Some(&begin.trusted_manifest_sha256),
            MAX_BUNDLE,
        )
        .map_err(|error| {
            if error.code == "limit_exceeded" {
                LIMIT
            } else {
                INVALID_ARGUMENT
            }
        })?;
        if bundle.manifest().profile != begin.profile {
            return Err(INVALID_ARGUMENT);
        }
        let parameters = TrustedParameters::from_bytes(
            unsafe { input(proof_parameters, proof_parameters_len, MAX_PARAMETERS)? },
            begin.k,
            &begin.proof_parameters_sha256,
        )
        .map_err(|_| INVALID_ARGUMENT)?;
        let ledger_parameters: ledger::structure::LedgerParameters =
            decode_tagged(unsafe { input(ledger_parameters, ledger_parameters_len, MAX_BYTES)? })?;
        let bundled_parameters: ledger::structure::LedgerParameters = decode_tagged(
            bundle
                .file(artifacts::Role::LedgerParameters)
                .map_err(|_| INVALID_ARGUMENT)?,
        )?;
        let plan: crate::Plan = serde_json::from_slice(
            bundle
                .file(artifacts::Role::Plan)
                .map_err(|_| INVALID_ARGUMENT)?,
        )
        .map_err(|_| INVALID_ARGUMENT)?;
        let circuit = crate::zkir::IrSource::load(
            bundle
                .file(artifacts::Role::Circuit)
                .map_err(|_| INVALID_ARGUMENT)?,
        )
        .map_err(|_| INVALID_ARGUMENT)?;
        if parameters.k() != begin.k
            || circuit.k() != begin.k
            || !circuit.do_communications_commitment
            || plan.entrypoint.is_empty()
            || !crate::profile::validate_plan(plan.target.as_deref(), plan.target_profile.as_ref())
        {
            return Err(INVALID_ARGUMENT);
        }
        let mut expected_parameters = bundled_parameters;
        expected_parameters.fee_prices = ledger_parameters.fee_prices.clone();
        if expected_parameters != ledger_parameters {
            return Err(INVALID_ARGUMENT);
        }

        let address_bytes: [u8; 32] = hex::decode(&begin.contract_address)
            .map_err(|_| INVALID_ARGUMENT)?
            .try_into()
            .map_err(|_| INVALID_ARGUMENT)?;
        let address = ContractAddress(HashOutput(address_bytes));
        let state: ContractState<crate::Db> =
            decode_tagged(unsafe { input(contract_state, contract_state_len, MAX_BYTES)? })?;
        let entry = EntryPointBuf(plan.entrypoint.as_bytes().to_vec());
        let verifier: VerifierKey = decode_tagged(
            bundle
                .file(artifacts::Role::VerifierKey)
                .map_err(|_| INVALID_ARGUMENT)?,
        )?;
        verifier.init().map_err(|_| INVALID_ARGUMENT)?;
        let matches_verifier = state
            .operations
            .get(&entry)
            .is_some_and(|operation| operation.latest() == Some(&verifier));
        if !matches_verifier {
            return Err(INVALID_ARGUMENT);
        }
        let mut snapshot = LedgerState::<crate::Db>::new(begin.network_id);
        snapshot.parameters = Sp::new(ledger_parameters.clone());
        snapshot.contract = snapshot.contract.insert(address, state.clone());

        let mut rng = unsafe { entropy(coins, coins_len)? };
        let mut source_inputs: BTreeMap<String, Json> =
            serde_json::from_slice(unsafe { input(inputs, inputs_len, MAX_BYTES)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        let execution = crate::prepare(
            &plan,
            &source_inputs,
            &state.data,
            &snapshot.parameters,
            address,
        );
        for value in source_inputs.values_mut() {
            crate::control::wipe_json(value);
        }
        drop(source_inputs);
        let execution = execution.map_err(|_| INVALID_ARGUMENT)?;

        let communication_commitment_rand = rng.r#gen();
        let checked = CheckedNativeCall {
            execution: &execution,
            circuit: &circuit,
            initial_context: QueryContext::new(state.data.clone(), address),
            entry_point: entry.clone(),
            communication_commitment_rand,
        };
        let offer = CompositionOffer::public_bytes(
            &checked
                .composition_offer(&snapshot.parameters)
                .map_err(|_| INVALID_ARGUMENT)?,
        )
        .map_err(|_| INVALID_ARGUMENT)?;
        if offer.len() > MAX_BYTES {
            return Err(LIMIT);
        }
        let owner = CompositionOwner {
            bundle,
            parameters,
            entry_point: entry,
            circuit,
            execution,
            snapshot,
            address,
            communication_commitment_rand,
            ttl: begin.ttl,
            proved: false,
        };
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                return Err(LIMIT);
            }
            let owner_token = r.token()?;
            let offer_token = r.result(offer)?;
            r.composition_owners.insert(
                owner_token,
                CompositionOwnerSlot {
                    owner: Arc::new(Mutex::new(owner)),
                    busy: false,
                },
            );
            unsafe {
                out_owner.write(owner_token);
                out_offer.write(offer_token);
            }
            Ok(())
        })
    })
}

/// # Safety
/// Draft bytes and entropy must remain readable until return. A successful owner
/// proof consumes this context; a rejected draft or slot leaves it available to retry.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_composition_owner_prove(
    owner: u64,
    draft: *const u8,
    draft_len: usize,
    slot: usize,
    coins: *const u8,
    coins_len: usize,
    out_proof: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_proof)? };
        let draft = unsafe { input(draft, draft_len, crate::composition_wire::MAX_DRAFT_BYTES)? };
        let rng = unsafe { entropy(coins, coins_len)? };
        let _work = Work::reserve()?;
        let owner_token = owner;
        let (_reservation, owner_arc) = CompositionOwnerReservation::reserve(owner_token)?;
        let mut owner = owner_arc.lock().map_err(|_| INTERNAL)?;
        if owner.proved {
            return Err(INVALID_STATE);
        }
        let draft = CompositionDraft::from_public_bytes(draft, &owner.snapshot)
            .map_err(|_| INVALID_RESPONSE)?;
        if draft.ttl() != owner.ttl {
            return Err(INVALID_RESPONSE);
        }
        let state = owner
            .snapshot
            .contract
            .get(&owner.address)
            .ok_or(INTERNAL)?;
        let call = CheckedNativeCall {
            execution: &owner.execution,
            circuit: &owner.circuit,
            initial_context: QueryContext::new(state.data.clone(), owner.address),
            entry_point: owner.entry_point.clone(),
            communication_commitment_rand: owner.communication_commitment_rand,
        };
        let proof = block_on(draft.prove_call(
            slot,
            &call,
            &owner.snapshot,
            &CompositionMaterial {
                bundle: &owner.bundle,
                parameters: &owner.parameters,
            },
            rng,
        ))
        .map_err(|_| INVALID_RESPONSE)?;
        if proof.len() > MAX_BYTES {
            return Err(LIMIT);
        }
        let proof_token = registry(|r| {
            let slot = r
                .composition_owners
                .get(&owner_token)
                .ok_or(INVALID_HANDLE)?;
            if !slot.busy {
                return Err(INTERNAL);
            }
            r.result(proof)
        })?;
        owner.proved = true;
        unsafe { out_proof.write(proof_token) };
        Ok(())
    })
}

#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub extern "C" fn noctium_native_composition_owner_free(owner: u64) -> i32 {
    guard(|| {
        registry(|r| {
            let slot = r.composition_owners.get(&owner).ok_or(INVALID_HANDLE)?;
            if slot.busy {
                return Err(INVALID_STATE);
            }
            r.composition_owners.remove(&owner).ok_or(INVALID_HANDLE)?;
            Ok(())
        })
    })
}

pub(crate) fn native_target_context_snapshot(
    token: u64,
) -> Result<crate::control::AuthenticatedNativeTarget, i32> {
    let _work = Work::reserve()?;
    let (directory, target) = registry(|r| {
        let context = r.targets.get(&token).ok_or(INVALID_HANDLE)?;
        if context.reservation.is_some() {
            return Err(INVALID_STATE);
        }
        Ok((
            context.bundle_directory.clone(),
            Arc::clone(&context.target),
        ))
    })?;
    let bundle =
        artifacts::verify_with_limit(&directory, Some(target.manifest_sha256()), MAX_BUNDLE)
            .map_err(|error| {
                if error.code == "limit_exceeded" {
                    LIMIT
                } else {
                    INVALID_ARGUMENT
                }
            })?;
    target
        .authenticated_control_target(token, &bundle)
        .map_err(|_| INVALID_ARGUMENT)
}

/// # Safety
/// All buffers must remain valid until return. State is private initial contract state.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_witness_target_begin(
    descriptor: *const u8,
    descriptor_len: usize,
    state_config: *const u8,
    state_config_len: usize,
    parameters: *const u8,
    parameters_len: usize,
    coins: *const u8,
    coins_len: usize,
    out_context: *mut u64,
    out_result: *mut u64,
) -> i32 {
    guard(|| {
        unsafe {
            output(out_context)?;
            output(out_result)?;
        }
        let begin: WitnessTargetBegin =
            serde_json::from_slice(unsafe { input(descriptor, descriptor_len, MAX_DESCRIPTOR)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        if begin.abi_version != 1
            || begin.profile != crate::profile::NAME
            || begin.bundle_directory.as_os_str().len() > 4096
            || begin.ttl == 0
        {
            return Err(INVALID_ARGUMENT);
        }
        let _work = Work::reserve()?;
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                Err(LIMIT)
            } else {
                Ok(())
            }
        })?;
        let bundle = artifacts::verify_with_limit(
            &begin.bundle_directory,
            Some(&begin.trusted_manifest_sha256),
            MAX_BUNDLE,
        )
        .map_err(|error| {
            if error.code == "limit_exceeded" {
                LIMIT
            } else {
                INVALID_ARGUMENT
            }
        })?;
        let parameters = TrustedParameters::from_bytes(
            unsafe { input(parameters, parameters_len, MAX_PARAMETERS)? },
            begin.k,
            &begin.proof_parameters_sha256,
        )
        .map_err(|_| INVALID_ARGUMENT)?;
        let mut rng = unsafe { entropy(coins, coins_len)? };
        let target = Arc::new(
            crate::proof::WitnessTarget::from_state_config(
                &bundle,
                unsafe { input(state_config, state_config_len, MAX_BYTES)? },
                &parameters,
                begin.ttl,
                &mut rng,
            )
            .map_err(|_| INVALID_ARGUMENT)?,
        );
        let result = encoded(json!({
            "abiVersion": 1,
            "status": "target_ready",
            "profile": crate::profile::NAME,
            "manifestSha256": target.manifest_sha256(),
            "contractAddress": target.contract_address(),
            "entrypoint": target.entrypoint(),
            "ttl": begin.ttl
        }))?;
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                return Err(LIMIT);
            }
            let context = r.token()?;
            let result = r.result(result)?;
            r.targets.insert(
                context,
                TargetContext {
                    bundle_directory: begin.bundle_directory,
                    target,
                    reservation: None,
                },
            );
            unsafe {
                out_context.write(context);
                out_result.write(result);
            }
            Ok(())
        })
    })
}

#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub extern "C" fn noctium_native_target_context_free(token: u64) -> i32 {
    guard(|| {
        registry(|r| {
            if r.targets
                .get(&token)
                .ok_or(INVALID_HANDLE)?
                .reservation
                .is_some()
            {
                return Err(INVALID_STATE);
            }
            r.targets.remove(&token).ok_or(INVALID_HANDLE)?;
            Ok(())
        })
    })
}

/// # Safety
/// Descriptor, SRS and entropy buffers must remain valid until return. Private inputs stay in
/// the completed Control session and are read only after bundle and SRS validation.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_begin_from_witness(
    descriptor: *const u8,
    descriptor_len: usize,
    target_context: u64,
    control_session: u64,
    parameters: *const u8,
    parameters_len: usize,
    coins: *const u8,
    coins_len: usize,
    out_session: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_session)? };
        let begin: WitnessProofBegin =
            serde_json::from_slice(unsafe { input(descriptor, descriptor_len, MAX_DESCRIPTOR)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        if begin.abi_version != 1
            || begin.profile != crate::profile::NAME
            || begin.max_response_bytes == 0
            || begin.max_response_bytes > MAX_BYTES
            || begin.proof_service_capability.is_empty()
            || begin.proof_service_capability.len() > 128
            || !begin
                .proof_service_capability
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b"._-".contains(&b))
        {
            return Err(INVALID_ARGUMENT);
        }
        let _work = Work::reserve()?;
        let (directory, target) = registry(|r| {
            if r.live_contexts() > MAX_SESSIONS {
                return Err(LIMIT);
            }
            let context = r.targets.get(&target_context).ok_or(INVALID_HANDLE)?;
            if context.reservation.is_some() {
                return Err(INVALID_STATE);
            }
            Ok((
                context.bundle_directory.clone(),
                Arc::clone(&context.target),
            ))
        })?;
        if !target.context_matches(&begin.trusted_manifest_sha256, &begin.profile, begin.ttl)
            || target.k() != begin.k
        {
            return Err(INVALID_ARGUMENT);
        }
        let bundle = artifacts::verify_with_limit(
            &directory,
            Some(&begin.trusted_manifest_sha256),
            MAX_BUNDLE,
        )
        .map_err(|error| {
            if error.code == "limit_exceeded" {
                LIMIT
            } else {
                INVALID_ARGUMENT
            }
        })?;
        let parameters = Arc::new(
            TrustedParameters::from_bytes(
                unsafe { input(parameters, parameters_len, MAX_PARAMETERS)? },
                begin.k,
                &begin.proof_parameters_sha256,
            )
            .map_err(|_| INVALID_ARGUMENT)?,
        );
        if parameters.sha256() != target.proof_parameters_sha256() {
            return Err(INVALID_ARGUMENT);
        }
        let authenticated_target = target
            .authenticated_control_target(target_context, &bundle)
            .map_err(|_| INVALID_ARGUMENT)?;
        let mut rng = unsafe { entropy(coins, coins_len)? };
        let mut inputs = crate::control_ffi::peek_completed_invocation(
            control_session,
            target_context,
            &authenticated_target.contract_address,
            &authenticated_target.entrypoint,
            &authenticated_target.control_plan,
            &authenticated_target.binding_bytes,
            &authenticated_target.relation,
        )?;
        let expected_inputs = inputs.try_clone_accounted().map_err(|_| LIMIT)?;
        let prepared = Arc::new(
            PreparedProof::from_witness_inputs(
                &bundle,
                &target,
                std::mem::take(&mut inputs.values),
                begin.ttl,
                &mut rng,
            )
            .map_err(|_| INVALID_ARGUMENT)?,
        );
        let (call_address, call_entrypoint) =
            prepared.call_target().map_err(|_| INVALID_ARGUMENT)?;
        if call_address != authenticated_target.contract_address
            || call_entrypoint != authenticated_target.entrypoint
        {
            return Err(INVALID_ARGUMENT);
        }
        let payload = prepared
            .private_request_payload(&parameters, begin.max_response_bytes)
            .map_err(|_| INVALID_ARGUMENT)?;
        if payload.len() > MAX_BYTES {
            return Err(LIMIT);
        }
        let public_parameters: ledger::structure::LedgerParameters = serialize::tagged_deserialize(
            bundle
                .file(crate::artifacts::Role::LedgerParameters)
                .map_err(|_| INVALID_ARGUMENT)?,
        )
        .map_err(|_| INVALID_ARGUMENT)?;
        let deployment = prepared
            .deployment_intent()
            .map(|intent| crate::native_client::prove_deployment(intent, &public_parameters))
            .transpose()
            .map_err(|_| INVALID_ARGUMENT)?;
        let reservation = registry(|r| {
            if r.live_contexts() > MAX_SESSIONS {
                return Err(LIMIT);
            }
            let context = r.targets.get(&target_context).ok_or(INVALID_HANDLE)?;
            if !Arc::ptr_eq(&context.target, &target) || context.reservation.is_some() {
                return Err(INVALID_STATE);
            }
            // The target occupies the slot that the proof session will replace. Reserve
            // both opaque IDs now so no capacity failure can happen after Control take.
            let reservation = ProofReservation {
                session: r.token()?,
                request_id: r.token()?,
            };
            r.targets
                .get_mut(&target_context)
                .ok_or(INVALID_HANDLE)?
                .reservation = Some(reservation);
            Ok(reservation)
        })?;

        // Do not hold the native registry mutex while Control takes its own registry lock.
        // The target reservation blocks free, concurrent proof begins and new Control starts.
        let completed = match crate::control_ffi::take_completed_invocation(
            control_session,
            target_context,
            &authenticated_target.control_plan,
            &authenticated_target.binding_bytes,
            &authenticated_target.relation,
            &expected_inputs,
            &authenticated_target.contract_address,
            &authenticated_target.entrypoint,
        ) {
            Ok(completed) => completed,
            Err(error) => {
                registry(|r| {
                    let context = r.targets.get_mut(&target_context).ok_or(INTERNAL)?;
                    if context.reservation != Some(reservation) {
                        return Err(INTERNAL);
                    }
                    context.reservation = None;
                    Ok(())
                })?;
                return Err(error);
            }
        };
        let crate::control::CompletedInvocation {
            context_id,
            mut inputs,
            runtime,
        } = completed;
        for value in inputs.values_mut() {
            crate::control::wipe_json(value);
        }
        registry(|r| {
            let context = r.targets.get(&target_context).ok_or(INTERNAL)?;
            if !Arc::ptr_eq(&context.target, &target) || context.reservation != Some(reservation) {
                return Err(INTERNAL);
            }
            r.targets.remove(&target_context);
            r.sessions.insert(
                reservation.session,
                Session {
                    prepared: Some(prepared),
                    parameters: Some(parameters),
                    payload,
                    request_id: reservation.request_id,
                    capability: begin.proof_service_capability,
                    manifest: begin.trusted_manifest_sha256,
                    max_response: begin.max_response_bytes,
                    phase: Phase::Pending,
                    local_started: false,
                    proved: None,
                    deployment,
                    client_started: [false; 2],
                    source_runtime: Some(runtime),
                    witness_context: Some(context_id),
                },
            );
            unsafe { out_session.write(reservation.session) };
            Ok(())
        })
    })
}

/// # Safety
/// Every pointer must reference the stated readable/writable memory until return. Entropy is 32 fresh secret bytes.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_begin(
    descriptor: *const u8,
    descriptor_len: usize,
    private_config: *const u8,
    private_len: usize,
    parameters: *const u8,
    parameters_len: usize,
    coins: *const u8,
    coins_len: usize,
    out_session: *mut u64,
) -> i32 {
    guard(|| {
        unsafe {
            output(out_session)?;
        }
        let begin: Begin =
            serde_json::from_slice(unsafe { input(descriptor, descriptor_len, MAX_DESCRIPTOR)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        if begin.abi_version != 1
            || begin.profile != crate::profile::NAME
            || begin.bundle_directory.as_os_str().len() > 4096
            || begin.proof_service_capability.is_empty()
            || begin.proof_service_capability.len() > 128
            || !begin
                .proof_service_capability
                .bytes()
                .all(|b| b.is_ascii_alphanumeric() || b"._-".contains(&b))
            || begin.max_response_bytes == 0
            || begin.max_response_bytes > MAX_BYTES
        {
            return Err(INVALID_ARGUMENT);
        }
        let _work = Work::reserve()?;
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                Err(LIMIT)
            } else {
                Ok(())
            }
        })?;
        let bundle = artifacts::verify_with_limit(
            &begin.bundle_directory,
            Some(&begin.trusted_manifest_sha256),
            MAX_BUNDLE,
        )
        .map_err(|error| {
            if error.code == "limit_exceeded" {
                LIMIT
            } else {
                INVALID_ARGUMENT
            }
        })?;
        let parameters = Arc::new(
            TrustedParameters::from_bytes(
                unsafe { input(parameters, parameters_len, MAX_PARAMETERS)? },
                begin.k,
                &begin.proof_parameters_sha256,
            )
            .map_err(|_| INVALID_ARGUMENT)?,
        );
        let mut rng = unsafe { entropy(coins, coins_len)? };
        // Retained public artifacts and SRS authenticate before private configuration is read.
        let prepared = Arc::new(
            PreparedProof::from_config(
                &bundle,
                unsafe { input(private_config, private_len, MAX_BYTES)? },
                begin.ttl,
                &mut rng,
            )
            .map_err(|_| INVALID_ARGUMENT)?,
        );
        let payload = prepared
            .private_request_payload(&parameters, begin.max_response_bytes)
            .map_err(|_| INVALID_ARGUMENT)?;
        if payload.len() > MAX_BYTES {
            return Err(LIMIT);
        }
        let public_parameters: ledger::structure::LedgerParameters = serialize::tagged_deserialize(
            bundle
                .file(crate::artifacts::Role::LedgerParameters)
                .map_err(|_| INVALID_ARGUMENT)?,
        )
        .map_err(|_| INVALID_ARGUMENT)?;
        let deployment = prepared
            .deployment_intent()
            .map(|intent| crate::native_client::prove_deployment(intent, &public_parameters))
            .transpose()
            .map_err(|_| INVALID_ARGUMENT)?;
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                return Err(LIMIT);
            }
            let token = r.token()?;
            let request_id = r.token()?;
            r.sessions.insert(
                token,
                Session {
                    prepared: Some(prepared),
                    parameters: Some(parameters),
                    payload,
                    request_id,
                    capability: begin.proof_service_capability,
                    manifest: begin.trusted_manifest_sha256,
                    max_response: begin.max_response_bytes,
                    phase: Phase::Pending,
                    local_started: false,
                    proved: None,
                    deployment,
                    client_started: [false; 2],
                    source_runtime: None,
                    witness_context: None,
                },
            );
            unsafe {
                out_session.write(token);
            }
            Ok(())
        })
    })
}
/// # Safety
/// out_result must reference a writable token. Request metadata is host-private transport.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_advance(session: u64, out_result: *mut u64) -> i32 {
    guard(|| {
        unsafe {
            output(out_result)?;
        }
        registry(|r| {
            let s = r.sessions.get(&session).ok_or(INVALID_HANDLE)?;
            let bytes = match &s.phase {
                Phase::Pending => encoded(
                    json!({"abiVersion":1,"status":"need_proof","requestId":s.request_id,
                    "operation":OPERATION,"capability":s.capability,"profile":crate::profile::NAME,
                    "encoding":"midnight-prove-v2","privatePayloadBytes":s.payload.len(),"maxResponseBytes":s.max_response,
                    "k":s.prepared.as_ref().ok_or(INTERNAL)?.k(),"srsSha256":s.parameters.as_ref().ok_or(INTERNAL)?.sha256(),
                    "sourceManifestSha256":s.manifest}),
                )?,
                Phase::Complete(bytes) => bytes.clone(),
                Phase::Cancelled => return Err(INVALID_STATE),
            };
            let token = r.result(bytes)?;
            unsafe {
                out_result.write(token);
            }
            Ok(())
        })
    })
}
/// # Safety
/// out_payload must reference a writable token. The returned token grants explicit private service access.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_private_request(
    session: u64,
    out_payload: *mut u64,
) -> i32 {
    guard(|| {
        unsafe {
            output(out_payload)?;
        }
        registry(|r| {
            if r.private.len() >= MAX_PRIVATE {
                return Err(LIMIT);
            }
            let s = r.sessions.get(&session).ok_or(INVALID_HANDLE)?;
            pending(s)?;
            let bytes = s.payload.clone();
            let token = r.token()?;
            r.private.insert(
                token,
                Private {
                    bytes,
                    owner: session,
                },
            );
            unsafe {
                out_payload.write(token);
            }
            Ok(())
        })
    })
}
/// # Safety
/// Reply metadata/proof must remain readable until return. No asynchronous work survives return.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_resume(
    session: u64,
    metadata: *const u8,
    metadata_len: usize,
    response: *const u8,
    response_len: usize,
    out_result: *mut u64,
) -> i32 {
    guard(|| {
        unsafe {
            output(out_result)?;
        }
        let reply: Reply =
            serde_json::from_slice(unsafe { input(metadata, metadata_len, MAX_DESCRIPTOR)? })
                .map_err(|_| INVALID_RESPONSE)?;
        let _work = Work::reserve()?;
        let (prepared, params, max) = registry(|r| {
            if r.results.len() >= MAX_RESULTS {
                return Err(LIMIT);
            }
            let s = r.sessions.get(&session).ok_or(INVALID_HANDLE)?;
            pending(s)?;
            if reply.abi_version != 1
                || reply.request_id != s.request_id
                || reply.operation != OPERATION
                || reply.capability != s.capability
                || reply.profile != crate::profile::NAME
            {
                return Err(INVALID_RESPONSE);
            }
            Ok((
                s.prepared.as_ref().ok_or(INTERNAL)?.clone(),
                s.parameters.as_ref().ok_or(INTERNAL)?.clone(),
                s.max_response,
            ))
        })?;
        let response = unsafe { input(response, response_len, max)? };
        let proved = block_on(prepared.attach_response(&params, response, max))
            .map_err(|_| INVALID_RESPONSE)?;
        let public = proved.public_serialized().map_err(|_| INTERNAL)?;
        let bytes = encoded(
            json!({"abiVersion":1,"status":"proved","profile":crate::profile::NAME,
            "publicIntentHex":hex::encode(&public),"publicIntentSha256":artifacts::digest(&public),
            "intentEncoding":"public-pedersen-commitment","funded":false,"submitted":false}),
        )?;
        registry(|r| {
            let s = r.sessions.get(&session).ok_or(INVALID_STATE)?;
            pending(s)?;
            if s.request_id != reply.request_id {
                return Err(INVALID_RESPONSE);
            }
            let token = r.result(bytes.clone())?;
            let s = r.sessions.get_mut(&session).ok_or(INTERNAL)?;
            s.phase = Phase::Complete(bytes);
            s.proved = Some(proved);
            s.payload.zeroize();
            s.prepared = None;
            s.parameters = None;
            r.revoke_private(session);
            unsafe {
                out_result.write(token);
            }
            Ok(())
        })
    })
}
/// # Safety
/// Fresh 32-byte host entropy and out_response must remain valid until return. This call performs CPU work.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_local_prove(
    payload: u64,
    coins: *const u8,
    coins_len: usize,
    out_response: *mut u64,
) -> i32 {
    guard(|| {
        unsafe {
            output(out_response)?;
        }
        let rng = unsafe { entropy(coins, coins_len)? };
        let _work = Work::reserve()?;
        let (owner, request, prepared, params, max) = registry(|r| {
            if r.results.len() >= MAX_RESULTS {
                return Err(LIMIT);
            }
            let owner = r.private.get(&payload).ok_or(INVALID_HANDLE)?.owner;
            let s = r.sessions.get_mut(&owner).ok_or(INVALID_HANDLE)?;
            pending(s)?;
            if s.local_started {
                return Err(INVALID_STATE);
            }
            s.local_started = true;
            Ok((
                owner,
                s.request_id,
                s.prepared.as_ref().ok_or(INTERNAL)?.clone(),
                s.parameters.as_ref().ok_or(INTERNAL)?.clone(),
                s.max_response,
            ))
        })?;
        let response =
            block_on(prepared.local_response(&params, max, rng)).map_err(|_| INVALID_RESPONSE)?;
        registry(|r| {
            let s = r.sessions.get(&owner).ok_or(INVALID_STATE)?;
            pending(s)?;
            if s.request_id != request {
                return Err(INVALID_STATE);
            }
            let token = r.result(response)?;
            unsafe {
                out_response.write(token);
            }
            Ok(())
        })
    })
}
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub extern "C" fn noctium_native_cancel(session: u64) -> i32 {
    guard(|| {
        registry(|r| {
            let s = r.sessions.get_mut(&session).ok_or(INVALID_HANDLE)?;
            pending(s)?;
            s.phase = Phase::Cancelled;
            s.payload.zeroize();
            s.prepared = None;
            s.parameters = None;
            s.source_runtime = None;
            s.witness_context = None;
            r.revoke_private(session);
            Ok(())
        })
    })
}
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub extern "C" fn noctium_native_free(session: u64) -> i32 {
    guard(|| {
        registry(|r| {
            r.sessions.remove(&session).ok_or(INVALID_HANDLE)?;
            r.revoke_private(session);
            Ok(())
        })
    })
}
unsafe fn length(token: u64, out: *mut usize, private: bool) -> i32 {
    guard(|| {
        if out.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        unsafe {
            out.write(0);
        }
        registry(|r| {
            let bytes = if private {
                &*r.private.get(&token).ok_or(INVALID_HANDLE)?.bytes
            } else {
                r.results.get(&token).ok_or(INVALID_HANDLE)?
            };
            unsafe {
                out.write(bytes.len());
            }
            Ok(())
        })
    })
}
unsafe fn copy(
    token: u64,
    buffer: *mut u8,
    capacity: usize,
    written: *mut usize,
    private: bool,
) -> i32 {
    guard(|| {
        if written.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        unsafe {
            written.write(0);
        }
        if buffer.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        registry(|r| {
            let bytes = if private {
                &*r.private.get(&token).ok_or(INVALID_HANDLE)?.bytes
            } else {
                r.results.get(&token).ok_or(INVALID_HANDLE)?
            };
            if capacity < bytes.len() {
                return Err(BUFFER_TOO_SMALL);
            }
            unsafe {
                std::ptr::copy_nonoverlapping(bytes.as_ptr(), buffer, bytes.len());
                written.write(bytes.len());
            }
            Ok(())
        })
    })
}
fn free(token: u64, private: bool) -> i32 {
    guard(|| {
        registry(|r| {
            if private {
                r.private.remove(&token).ok_or(INVALID_HANDLE)?;
            } else {
                r.results.remove(&token).ok_or(INVALID_HANDLE)?;
            }
            Ok(())
        })
    })
}
macro_rules! buffers {
    ($len:ident,$copy:ident,$free:ident,$private:expr) => {
        /// # Safety
        /// out must reference writable size_t memory.
        #[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
        pub unsafe extern "C" fn $len(token: u64, out: *mut usize) -> i32 {
            unsafe { length(token, out, $private) }
        }
        /// # Safety
        /// buffer must reference capacity writable bytes and written a writable size_t.
        #[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
        pub unsafe extern "C" fn $copy(
            token: u64,
            buffer: *mut u8,
            capacity: usize,
            written: *mut usize,
        ) -> i32 {
            unsafe { copy(token, buffer, capacity, written, $private) }
        }
        #[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
        pub extern "C" fn $free(token: u64) -> i32 {
            free(token, $private)
        }
    };
}
buffers!(
    noctium_native_result_length,
    noctium_native_result_copy,
    noctium_native_result_free,
    false
);
buffers!(
    noctium_native_private_length,
    noctium_native_private_copy,
    noctium_native_private_free,
    true
);

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn live_work_slots_survive_cancellation_and_free_until_owned_work_returns() {
        let first = Work::reserve().unwrap();
        let second = Work::reserve().unwrap();
        let (a, b) = registry(|r| {
            let a = r.token()?;
            let b = r.token()?;
            for id in [a, b] {
                r.sessions.insert(
                    id,
                    Session {
                        prepared: None,
                        parameters: None,
                        payload: Zeroizing::new(vec![7; 32]),
                        request_id: id,
                        capability: "test".into(),
                        manifest: "0".repeat(64),
                        max_response: MAX_BYTES,
                        phase: Phase::Pending,
                        local_started: true,
                        proved: None,
                        deployment: None,
                        client_started: [false; 2],
                        source_runtime: None,
                        witness_context: None,
                    },
                );
            }
            Ok((a, b))
        })
        .unwrap();
        assert_eq!(noctium_native_cancel(a), OK);
        assert_eq!(noctium_native_free(a), OK);
        assert_eq!(noctium_native_free(b), OK);
        assert!(matches!(Work::reserve(), Err(LIMIT)));
        drop(first);
        let replacement = Work::reserve().unwrap();
        assert!(matches!(Work::reserve(), Err(LIMIT)));
        drop(second);
        drop(replacement);
        assert_eq!(registry(|r| Ok(r.active_work)), Ok(0));
    }
}

// Phase-B tokens carry typed Rust service objects, never caller-claimed receipt fields.
#[derive(Clone)]
pub(crate) struct ServiceRequest {
    pub owner: u64,
    pub request: Arc<crate::native_client::Request>,
}
struct ServiceResponse {
    owner: u64,
    request_id: u64,
    value: crate::native_client::ServiceReply,
}
const MAX_SERVICES: usize = 16;
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct ClientReply {
    abi_version: u32,
    request_id: String,
    operation: String,
    capability: String,
    schema: String,
    profile: String,
}
fn client_revoke(r: &mut Registry, owner: u64) {
    r.requests.retain(|_, q| q.owner != owner);
    r.replies.retain(|_, q| q.owner != owner);
    r.revoke_private(owner);
}
struct ClientLease {
    token: u64,
    driver: Option<crate::native_client::Driver>,
}
impl ClientLease {
    fn take(token: u64) -> Result<Self, i32> {
        registry(|r| {
            let slot = r.clients.get_mut(&token).ok_or(INVALID_HANDLE)?;
            let driver = slot.take().ok_or(INVALID_STATE)?;
            Ok(Self {
                token,
                driver: Some(driver),
            })
        })
    }
    fn driver(&mut self) -> Result<&mut crate::native_client::Driver, i32> {
        self.driver.as_mut().ok_or(INTERNAL)
    }
}
impl Drop for ClientLease {
    fn drop(&mut self) {
        let value = self.driver.take();
        let _ = registry(|r| {
            let slot = r.clients.get_mut(&self.token).ok_or(INTERNAL)?;
            *slot = value;
            Ok(())
        });
    }
}
fn client_poll(token: u64) -> Result<serde_json::Value, i32> {
    let _work = Work::reserve()?;
    let mut lease = ClientLease::take(token)?;
    lease.driver()?.poll().map_err(|_| INVALID_STATE)?;
    let status = lease.driver()?.status();
    drop(lease);
    registry(|r| {
        if r.clients
            .get(&token)
            .and_then(Option::as_ref)
            .and_then(|d| d.request())
            .is_none()
        {
            client_revoke(r, token)
        }
        Ok(())
    })?;
    Ok(status)
}
fn client_result(value: serde_json::Value, out: *mut u64) -> Result<(), i32> {
    let bytes = encoded(value)?;
    registry(|r| {
        let token = r.result(bytes)?;
        unsafe { out.write(token) }
        Ok(())
    })
}
pub(crate) fn service_request(token: u64) -> Result<ServiceRequest, i32> {
    registry(|r| {
        if r.replies.len() >= MAX_SERVICES {
            return Err(LIMIT);
        }
        let q = r.requests.get(&token).ok_or(INVALID_HANDLE)?;
        let current = r
            .clients
            .get(&q.owner)
            .and_then(Option::as_ref)
            .and_then(|d| d.request())
            .ok_or(INVALID_STATE)?;
        if current.id != q.request.id {
            return Err(INVALID_STATE);
        }
        Ok(q.clone())
    })
}
pub(crate) fn service_reply(
    token: u64,
    value: crate::native_client::ServiceReply,
) -> Result<u64, i32> {
    registry(|r| {
        if r.replies.len() >= MAX_SERVICES {
            return Err(LIMIT);
        }
        let q = r.requests.get(&token).ok_or(INVALID_HANDLE)?;
        let current = r
            .clients
            .get(&q.owner)
            .and_then(Option::as_ref)
            .and_then(|d| d.request())
            .ok_or(INVALID_STATE)?;
        if current.id != q.request.id || !current.accepts(&value) {
            return Err(INVALID_RESPONSE);
        }
        let owner = q.owner;
        let request_id = q.request.id;
        let token = r.token()?;
        r.replies.insert(
            token,
            ServiceResponse {
                owner,
                request_id,
                value,
            },
        );
        Ok(token)
    })
}
/// # Safety
/// All input/output pointers must remain valid until return. Setup is a separate private channel.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_start(
    source: u64,
    kind: u32,
    descriptor: *const u8,
    descriptor_len: usize,
    setup: *const u8,
    setup_len: usize,
    out_client: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_client)? };
        if kind > 1 {
            return Err(INVALID_ARGUMENT);
        }
        let descriptor: crate::native_client::Descriptor =
            serde_json::from_slice(unsafe { input(descriptor, descriptor_len, MAX_DESCRIPTOR)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        let setup = unsafe { input(setup, setup_len, MAX_BYTES)? };
        let _work = Work::reserve()?;
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                return Err(LIMIT);
            }
            let s = r.sessions.get(&source).ok_or(INVALID_HANDLE)?;
            if !matches!(s.phase, Phase::Complete(_)) || s.client_started[kind as usize] {
                return Err(INVALID_STATE);
            }
            if kind == 1 && s.source_runtime.is_some() {
                return Err(INVALID_STATE);
            }
            let proved = s.proved.as_ref().ok_or(INVALID_STATE)?;
            let Some(ledger::structure::ContractAction::Call(call)) =
                proved.native().actions.iter_deref().next()
            else {
                return Err(INTERNAL);
            };
            let contract = if kind == 0 {
                let deploy = s.deployment.as_ref().ok_or(INVALID_STATE)?;
                let Some(ledger::structure::ContractAction::Deploy(d)) =
                    deploy.actions.iter_deref().next()
                else {
                    return Err(INTERNAL);
                };
                if d.address() != call.address {
                    return Err(INTERNAL);
                }
                crate::native_client::Contract::Deployment {
                    intent: deploy.clone(),
                    entrypoint: String::from_utf8(call.entry_point.0.clone())
                        .map_err(|_| INTERNAL)?,
                }
            } else {
                crate::native_client::Contract::Proved(proved.native().clone())
            };
            let driver = crate::native_client::Driver::start(descriptor, setup, contract)
                .map_err(|_| INVALID_ARGUMENT)?;
            let token = r.token()?;
            r.clients.insert(token, Some(driver));
            r.sessions.get_mut(&source).ok_or(INTERNAL)?.client_started[kind as usize] = true;
            unsafe { out_client.write(token) }
            Ok(())
        })
    })
}

/// # Safety
/// Descriptor and output buffers must remain valid until return. The owned source Runtime is
/// consumed only after target, descriptor and recovery-envelope checks succeed.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_start_from_witness(
    source: u64,
    descriptor: *const u8,
    descriptor_len: usize,
    out_client: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_client)? };
        let descriptor: crate::native_client::Descriptor =
            serde_json::from_slice(unsafe { input(descriptor, descriptor_len, MAX_DESCRIPTOR)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        let _work = Work::reserve()?;
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                return Err(LIMIT);
            }
            let token = r.token()?;
            let session = r.sessions.get_mut(&source).ok_or(INVALID_HANDLE)?;
            if !matches!(session.phase, Phase::Complete(_))
                || session.client_started[1]
                || session.witness_context.is_none()
            {
                return Err(INVALID_STATE);
            }
            let proved = session.proved.as_ref().ok_or(INVALID_STATE)?;
            let contract = crate::native_client::Contract::Proved(proved.native().clone());
            let driver = crate::native_client::Driver::start_with_runtime(
                descriptor,
                &mut session.source_runtime,
                contract,
            )
            .map_err(|_| INVALID_ARGUMENT)?;
            session.client_started[1] = true;
            r.clients.insert(token, Some(driver));
            unsafe { out_client.write(token) };
            Ok(())
        })
    })
}
/// # Safety
/// Descriptor/context and writable output token must remain valid until return. No private witness is required.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_recover(
    descriptor: *const u8,
    descriptor_len: usize,
    context: *const u8,
    context_len: usize,
    out_client: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_client)? };
        let d =
            serde_json::from_slice(unsafe { input(descriptor, descriptor_len, MAX_DESCRIPTOR)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        let context = unsafe { input(context, context_len, MAX_RECOVERY_CONTEXT)? };
        let driver =
            crate::native_client::Driver::recover(d, context).map_err(|_| INVALID_ARGUMENT)?;
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                return Err(LIMIT);
            }
            let token = r.token()?;
            r.clients.insert(token, Some(driver));
            unsafe { out_client.write(token) }
            Ok(())
        })
    })
}
/// # Safety
/// command bytes and writable output token must remain valid until return.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_command(
    client: u64,
    command: *const u8,
    command_len: usize,
    out_result: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_result)? };
        let command = std::str::from_utf8(unsafe { input(command, command_len, 32)? })
            .ok()
            .and_then(crate::native_client::Command::parse)
            .ok_or(INVALID_ARGUMENT)?;
        {
            let mut lease = ClientLease::take(client)?;
            lease
                .driver()?
                .command(command)
                .map_err(|_| INVALID_STATE)?;
        }
        client_result(client_poll(client)?, out_result)
    })
}
/// # Safety
/// out_result must reference a writable token.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_advance(client: u64, out_result: *mut u64) -> i32 {
    guard(|| {
        unsafe { output(out_result)? };
        client_result(client_poll(client)?, out_result)
    })
}
/// # Safety
/// out_request must reference a writable opaque service token.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_request(client: u64, out_request: *mut u64) -> i32 {
    guard(|| {
        unsafe { output(out_request)? };
        registry(|r| {
            if r.requests.len() >= MAX_SERVICES {
                return Err(LIMIT);
            }
            let request = r
                .clients
                .get(&client)
                .ok_or(INVALID_HANDLE)?
                .as_ref()
                .ok_or(INVALID_STATE)?
                .request()
                .ok_or(INVALID_STATE)?;
            let token = r.token()?;
            r.requests.insert(
                token,
                ServiceRequest {
                    owner: client,
                    request,
                },
            );
            unsafe { out_request.write(token) }
            Ok(())
        })
    })
}
/// # Safety
/// Reply correlation metadata/output token must remain valid until return. Reply payload is a checked Rust token.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_resume(
    client: u64,
    metadata: *const u8,
    metadata_len: usize,
    reply: u64,
    out_result: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_result)? };
        let m: ClientReply =
            serde_json::from_slice(unsafe { input(metadata, metadata_len, MAX_DESCRIPTOR)? })
                .map_err(|_| INVALID_RESPONSE)?;
        let id = m
            .request_id
            .parse::<u64>()
            .ok()
            .filter(|v| v.to_string() == m.request_id && *v > 0)
            .ok_or(INVALID_RESPONSE)?;
        registry(|r| {
            let d = r
                .clients
                .get(&client)
                .ok_or(INVALID_HANDLE)?
                .as_ref()
                .ok_or(INVALID_STATE)?;
            let q = d.request().ok_or(INVALID_STATE)?;
            let response = r.replies.get(&reply).ok_or(INVALID_HANDLE)?;
            if m.abi_version != 1
                || m.profile != crate::profile::NAME
                || m.operation != q.operation
                || m.capability != q.capability
                || m.schema != q.schema
                || id != q.id
                || response.owner != client
                || response.request_id != id
                || !q.accepts(&response.value)
            {
                return Err(INVALID_RESPONSE);
            }
            let value = r.replies.remove(&reply).ok_or(INTERNAL)?.value;
            r.clients
                .get(&client)
                .and_then(Option::as_ref)
                .ok_or(INVALID_STATE)?
                .complete(id, value)
                .map_err(|_| INVALID_RESPONSE)?;
            client_revoke(r, client);
            Ok(())
        })?;
        client_result(client_poll(client)?, out_result)
    })
}
/// # Safety
/// out_reply must reference writable memory. This explicitly reports a host service failure, never rejection evidence.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_service_failure(request: u64, out_reply: *mut u64) -> i32 {
    guard(|| {
        unsafe { output(out_reply)? };
        let token = service_reply(request, crate::native_client::ServiceReply::Failure)?;
        unsafe { out_reply.write(token) }
        Ok(())
    })
}
/// # Safety
/// out_payload must reference writable memory. This separate token contains private native bytes.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_private_request(
    request: u64,
    out_payload: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_payload)? };
        let _work = Work::reserve()?;
        let q = service_request(request)?;
        let bytes = q.request.private_bytes().map_err(|_| INVALID_STATE)?;
        if bytes.len() > 32 * 1024 * 1024 {
            return Err(LIMIT);
        }
        registry(|r| {
            if r.private.len() >= MAX_PRIVATE {
                return Err(LIMIT);
            }
            let current = r
                .clients
                .get(&q.owner)
                .and_then(Option::as_ref)
                .and_then(|d| d.request())
                .ok_or(INVALID_STATE)?;
            if current.id != q.request.id {
                return Err(INVALID_STATE);
            }
            let token = r.token()?;
            r.private.insert(
                token,
                Private {
                    bytes,
                    owner: q.owner,
                },
            );
            unsafe { out_payload.write(token) }
            Ok(())
        })
    })
}
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub extern "C" fn noctium_client_service_free(token: u64) -> i32 {
    guard(|| {
        registry(|r| {
            if r.requests.remove(&token).is_none() && r.replies.remove(&token).is_none() {
                return Err(INVALID_HANDLE);
            }
            Ok(())
        })
    })
}
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub extern "C" fn noctium_client_detach(client: u64) -> i32 {
    guard(|| {
        registry(|r| {
            let d = r
                .clients
                .get(&client)
                .ok_or(INVALID_HANDLE)?
                .as_ref()
                .ok_or(INVALID_STATE)?;
            if !d.detachable() {
                return Err(INVALID_STATE);
            }
            r.clients.remove(&client);
            r.contract_client_targets.remove(&client);
            client_revoke(r, client);
            Ok(())
        })
    })
}
unsafe fn client_bytes(client: u64, out: *mut u64, state: bool) -> i32 {
    guard(|| {
        unsafe { output(out)? };
        let lease = ClientLease::take(client)?;
        let d = lease.driver.as_ref().ok_or(INTERNAL)?;
        let bytes = if state {
            d.receipt_state()
        } else {
            d.transaction()
        }
        .map_err(|_| INVALID_STATE)?;
        if bytes.len() > if state { MAX_BYTES } else { 4 * MAX_BYTES } {
            return Err(LIMIT);
        }
        drop(lease);
        registry(|r| {
            if r.results.len() >= MAX_RESULTS {
                return Err(LIMIT);
            }
            let token = r.token()?;
            r.results.insert(token, bytes);
            unsafe { out.write(token) }
            Ok(())
        })
    })
}
/// # Safety
/// out_result must reference writable memory. Returns only sealed public native transaction bytes.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_transaction(client: u64, out_result: *mut u64) -> i32 {
    unsafe { client_bytes(client, out_result, false) }
}
/// # Safety
/// out_result must reference writable memory. Returns full checked finalized public contract state.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_receipt_state(client: u64, out_result: *mut u64) -> i32 {
    unsafe { client_bytes(client, out_result, true) }
}

/// # Safety
/// out_private must reference writable memory. The context contains private host data.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_recovery_context(client: u64, out_private: *mut u64) -> i32 {
    guard(|| {
        unsafe { output(out_private)? };
        registry(|r| {
            if r.private.len() >= MAX_PRIVATE {
                return Err(LIMIT);
            }
            let token = r.token()?;
            let context = r
                .clients
                .get(&client)
                .ok_or(INVALID_HANDLE)?
                .as_ref()
                .and_then(crate::native_client::Driver::recovery_context)
                .ok_or(INVALID_STATE)?;
            if context.len() > MAX_RECOVERY_CONTEXT {
                return Err(LIMIT);
            }
            let bytes = Zeroizing::new(context.to_vec());
            r.private.insert(token, Private { bytes, owner: client });
            unsafe { out_private.write(token) };
            Ok(())
        })
    })
}

pub(crate) fn service_public_bytes(bytes: Vec<u8>) -> Result<u64, i32> {
    registry(|r| r.result(bytes))
}
#[cfg(feature = "localnet")]
pub(crate) fn service_private_bytes(owner: u64, bytes: Zeroizing<Vec<u8>>) -> Result<u64, i32> {
    registry(|r| {
        if bytes.len() > MAX_BYTES || r.private.len() >= MAX_PRIVATE {
            return Err(LIMIT);
        }
        let token = r.token()?;
        r.private.insert(token, Private { bytes, owner });
        Ok(token)
    })
}
#[cfg(feature = "localnet")]
pub(crate) fn service_private_revoke(owner: u64) {
    let _ = registry(|r| {
        r.revoke_private(owner);
        Ok(())
    });
}

fn validate_contract_target_begin(begin: &ContractTargetBegin) -> Result<(), i32> {
    if begin.abi_version != 1
        || begin.profile != crate::profile::NAME
        || begin.ttl == 0
        || begin.operations.is_empty()
        || begin.operations.len() > artifacts::MAX_ENTRIES
        || begin.journal_directory.as_os_str().len() > 4096
        || !begin.journal_directory.is_absolute()
    {
        return Err(INVALID_ARGUMENT);
    }
    Ok(())
}

fn verify_contract_bundle_set(
    begin: &ContractTargetBegin,
) -> Result<artifacts::ContractBundleSet, i32> {
    let mut total_bytes = 0u64;
    let mut bundles = Vec::with_capacity(begin.operations.len());
    for operation in &begin.operations {
        if operation.bundle_directory.as_os_str().len() > 4096 {
            return Err(INVALID_ARGUMENT);
        }
        let bundle = artifacts::verify_with_limit(
            &operation.bundle_directory,
            Some(&operation.trusted_manifest_sha256),
            MAX_BUNDLE,
        )
        .map_err(|error| {
            if error.code == "limit_exceeded" {
                LIMIT
            } else {
                INVALID_ARGUMENT
            }
        })?;
        if bundle.manifest().profile != begin.profile {
            return Err(INVALID_ARGUMENT);
        }
        total_bytes = bundle
            .manifest()
            .entries
            .iter()
            .try_fold(total_bytes, |sum, entry| sum.checked_add(entry.size))
            .filter(|sum| *sum <= MAX_BUNDLE)
            .ok_or(LIMIT)?;
        bundles.push(bundle);
    }
    artifacts::ContractBundleSet::new(bundles).map_err(|error| {
        if error.code == "limit_exceeded" {
            LIMIT
        } else {
            INVALID_ARGUMENT
        }
    })
}

fn contract_target_metadata(
    target: &crate::proof::WitnessContractTarget,
    contract_name: &str,
    operations: &[String],
    ttl: u64,
) -> Result<Vec<u8>, i32> {
    encoded(json!({
        "abiVersion": 1,
        "status": "contract_target_ready",
        "profile": crate::profile::NAME,
        "contractName": contract_name,
        "contractSetIdentity": target.identity(),
        "contractAddress": target.contract_address(),
        "operations": operations,
        "ttl": ttl
    }))
}

fn contract_set_details(bundles: &artifacts::ContractBundleSet) -> (String, Vec<String>) {
    (
        bundles.contract_name().to_owned(),
        bundles
            .iter()
            .map(|(operation, _)| operation.to_owned())
            .collect(),
    )
}

/// # Safety
/// All byte channels must stay readable and immutable until return. `state_config` contains
/// private initial contract state. `coins` must contain 32 bytes of fresh host entropy.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_contract_target_begin(
    descriptor: *const u8,
    descriptor_len: usize,
    state_config: *const u8,
    state_config_len: usize,
    coins: *const u8,
    coins_len: usize,
    out_target: *mut u64,
    out_metadata: *mut u64,
) -> i32 {
    guard(|| {
        unsafe {
            output(out_target)?;
            output(out_metadata)?;
        }
        let begin: ContractTargetBegin =
            serde_json::from_slice(unsafe { input(descriptor, descriptor_len, MAX_DESCRIPTOR)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        validate_contract_target_begin(&begin)?;
        let _work = Work::reserve()?;
        let bundles = verify_contract_bundle_set(&begin)?;
        let (contract_name, operations) = contract_set_details(&bundles);
        let mut rng = unsafe { entropy(coins, coins_len)? };
        let target = crate::proof::WitnessContractTarget::from_state_config(
            bundles,
            unsafe { input(state_config, state_config_len, MAX_BYTES)? },
            begin.ttl,
            &mut rng,
        )
        .map_err(|_| INVALID_ARGUMENT)?;
        let metadata = contract_target_metadata(&target, &contract_name, &operations, begin.ttl)?;
        let target = Arc::new(target);
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                return Err(LIMIT);
            }
            let target_token = r.token()?;
            let metadata_token = r.result(metadata)?;
            r.contract_targets.insert(
                target_token,
                ContractTargetSlot {
                    target,
                    #[cfg(feature = "localnet")]
                    journal_directory: begin.journal_directory,
                    busy: false,
                    deployment_started: false,
                },
            );
            unsafe {
                out_target.write(target_token);
                out_metadata.write(metadata_token);
            }
            Ok(())
        })
    })
}

/// # Safety
/// Same buffers as target_begin plus a public SDK60 deployment attempt identity. The explicit
/// journal directory is host-authorized and contains the durable deployment attempt.
#[cfg(feature = "localnet")]
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_contract_target_restore(
    descriptor: *const u8,
    descriptor_len: usize,
    state_config: *const u8,
    state_config_len: usize,
    coins: *const u8,
    coins_len: usize,
    deployment_attempt_id: *const u8,
    deployment_attempt_id_len: usize,
    out_target: *mut u64,
    out_metadata: *mut u64,
) -> i32 {
    guard(|| {
        unsafe {
            output(out_target)?;
            output(out_metadata)?;
        }
        let begin: ContractTargetBegin =
            serde_json::from_slice(unsafe { input(descriptor, descriptor_len, MAX_DESCRIPTOR)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        validate_contract_target_begin(&begin)?;
        let attempt_id = std::str::from_utf8(unsafe {
            input(deployment_attempt_id, deployment_attempt_id_len, 256)?
        })
        .map_err(|_| INVALID_ARGUMENT)?;
        let _work = Work::reserve()?;
        let bundles = verify_contract_bundle_set(&begin)?;
        let (contract_name, operations) = contract_set_details(&bundles);
        let mut rng = unsafe { entropy(coins, coins_len)? };
        let target = crate::proof::WitnessContractTarget::from_state_config(
            bundles,
            unsafe { input(state_config, state_config_len, MAX_BYTES)? },
            begin.ttl,
            &mut rng,
        )
        .map_err(|_| INVALID_ARGUMENT)?;
        let store = crate::localnet::journal::DirectoryJournal::new(
            &begin.journal_directory,
            Duration::from_secs(2),
        )
        .map_err(|_| INVALID_ARGUMENT)?;
        let target = block_on(
            target.restore_deployment_from_journal(&store, attempt_id, begin.ttl, &mut rng),
        )
        .map_err(|_| INVALID_RESPONSE)?;
        let metadata = contract_target_metadata(&target, &contract_name, &operations, begin.ttl)?;
        let target = Arc::new(target);
        registry(|r| {
            if r.live_contexts() >= MAX_SESSIONS {
                return Err(LIMIT);
            }
            let target_token = r.token()?;
            let metadata_token = r.result(metadata)?;
            r.contract_targets.insert(
                target_token,
                ContractTargetSlot {
                    target,
                    journal_directory: begin.journal_directory,
                    busy: false,
                    deployment_started: true,
                },
            );
            unsafe {
                out_target.write(target_token);
                out_metadata.write(metadata_token);
            }
            Ok(())
        })
    })
}

#[cfg(not(feature = "localnet"))]
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_contract_target_restore(
    _descriptor: *const u8,
    _descriptor_len: usize,
    _state_config: *const u8,
    _state_config_len: usize,
    _coins: *const u8,
    _coins_len: usize,
    _deployment_attempt_id: *const u8,
    _deployment_attempt_id_len: usize,
    out_target: *mut u64,
    out_metadata: *mut u64,
) -> i32 {
    guard(|| {
        unsafe {
            output(out_target)?;
            output(out_metadata)?;
        }
        Err(INVALID_STATE)
    })
}

/// # Safety
/// `operation`, client descriptor and private setup buffers must remain valid until return.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_contract_deployment_start(
    target: u64,
    operation: *const u8,
    operation_len: usize,
    client_descriptor: *const u8,
    client_descriptor_len: usize,
    setup: *const u8,
    setup_len: usize,
    out_client: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_client)? };
        let operation = std::str::from_utf8(unsafe { input(operation, operation_len, 256)? })
            .map_err(|_| INVALID_ARGUMENT)?;
        let descriptor =
            unsafe { input(client_descriptor, client_descriptor_len, MAX_DESCRIPTOR)? };
        let setup = unsafe { input(setup, setup_len, MAX_BYTES)? };
        let _work = Work::reserve()?;
        let target_reservation = ContractTargetReservation::reserve(target)?;
        if target_reservation.deployment_started {
            return Err(INVALID_STATE);
        }
        let registration = ContractClientRegistration::reserve()?;
        let client = target_reservation
            .target
            .start_deployment_client(operation, descriptor, setup)
            .map_err(|_| INVALID_ARGUMENT)?;
        let client_token = registration.commit(
            client.into_driver(),
            target,
            Arc::clone(&target_reservation.target),
            true,
        )?;
        unsafe { out_client.write(client_token) };
        Ok(())
    })
}

/// # Safety
/// Output points to a writable u64. The SDK issues one state token only after finalized receipt
/// verification and durable compare-and-set completion.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_contract_state_take(
    client: u64,
    out_state: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_state)? };
        let _work = Work::reserve()?;
        registry(|r| {
            if !r.clients.contains_key(&client) {
                return Err(INVALID_HANDLE);
            }
            if !r.contract_client_targets.contains_key(&client) {
                return Err(INVALID_STATE);
            }
            Ok(())
        })?;
        let registration = ContractStateRegistration::reserve()?;
        let mut lease = ClientLease::take(client)?;
        let current = lease
            .driver()?
            .current_state_context()
            .map_err(|_| INVALID_STATE)?;
        drop(lease);
        let state_token = registration.commit(current)?;
        unsafe { out_state.write(state_token) };
        Ok(())
    })
}

/// # Safety
/// All byte channels must remain readable and immutable until return. Private scalar inputs are
/// parsed only after the authenticated target and operation have been selected.
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_client_contract_call_start(
    target: u64,
    state: u64,
    call_descriptor: *const u8,
    call_descriptor_len: usize,
    inputs: *const u8,
    inputs_len: usize,
    srs: *const u8,
    srs_len: usize,
    coins: *const u8,
    coins_len: usize,
    client_descriptor: *const u8,
    client_descriptor_len: usize,
    setup: *const u8,
    setup_len: usize,
    out_client: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_client)? };
        let begin: ContractCallBegin = serde_json::from_slice(unsafe {
            input(call_descriptor, call_descriptor_len, MAX_DESCRIPTOR)?
        })
        .map_err(|_| INVALID_ARGUMENT)?;
        if begin.abi_version != 1 || begin.operation.is_empty() || begin.ttl == 0 {
            return Err(INVALID_ARGUMENT);
        }
        let srs = unsafe { input(srs, srs_len, MAX_PARAMETERS)? };
        let descriptor =
            unsafe { input(client_descriptor, client_descriptor_len, MAX_DESCRIPTOR)? };
        let setup = unsafe { input(setup, setup_len, MAX_BYTES)? };
        let _work = Work::reserve()?;
        let target_reservation = ContractTargetReservation::reserve(target)?;
        if !target_reservation.deployment_started {
            return Err(INVALID_STATE);
        }
        let parameters =
            TrustedParameters::from_bytes(srs, begin.k, &begin.proof_parameters_sha256)
                .map_err(|_| INVALID_ARGUMENT)?;
        let operation = target_reservation
            .target
            .operation(&begin.operation, &parameters, begin.ttl)
            .map_err(|_| INVALID_ARGUMENT)?;
        if operation
            .bundle()
            .map_err(|_| INVALID_ARGUMENT)?
            .manifest()
            .entries
            .iter()
            .any(|entry| entry.role == artifacts::Role::WitnessControl)
        {
            return Err(INVALID_ARGUMENT);
        }
        let mut inputs = NativePrivateInputs(
            serde_json::from_slice(unsafe { input(inputs, inputs_len, MAX_BYTES)? })
                .map_err(|_| INVALID_ARGUMENT)?,
        );
        let mut current = ContractStateReservation::reserve(state)?;
        let registration = ContractClientRegistration::reserve()?;
        let mut rng = unsafe { entropy(coins, coins_len)? };
        let prepared = PreparedProof::from_contract_witness_inputs(
            &operation,
            current.current()?,
            std::mem::take(&mut inputs.0),
            &mut rng,
        )
        .map_err(|_| INVALID_ARGUMENT)?;
        let response = Zeroizing::new(
            block_on(prepared.local_response(&parameters, MAX_BYTES, &mut rng))
                .map_err(|_| INVALID_RESPONSE)?,
        );
        let proved = block_on(prepared.attach_response(&parameters, &response, MAX_BYTES))
            .map_err(|_| INVALID_RESPONSE)?;
        let mut proved = Some(proved);
        let client = target_reservation
            .target
            .start_call_client(&operation, &mut proved, descriptor, setup)
            .map_err(|_| INVALID_ARGUMENT)?;
        let client_token = registration.commit(
            client.into_driver(),
            target,
            Arc::clone(&target_reservation.target),
            false,
        )?;
        current.consume();
        unsafe { out_client.write(client_token) };
        Ok(())
    })
}

/// # Safety
/// The explicit host journal context and SDK60 descriptor must remain readable until return.
#[cfg(feature = "localnet")]
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_contract_call_recover(
    target: u64,
    call_attempt_id: *const u8,
    call_attempt_id_len: usize,
    client_descriptor: *const u8,
    client_descriptor_len: usize,
    host_context: *const u8,
    host_context_len: usize,
    out_client: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_client)? };
        let attempt_id =
            std::str::from_utf8(unsafe { input(call_attempt_id, call_attempt_id_len, 256)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        let descriptor =
            unsafe { input(client_descriptor, client_descriptor_len, MAX_DESCRIPTOR)? };
        let context = unsafe { input(host_context, host_context_len, MAX_RECOVERY_CONTEXT)? };
        let _work = Work::reserve()?;
        let target_reservation = ContractTargetReservation::reserve(target)?;
        let registration = ContractClientRegistration::reserve()?;
        let client = {
            let store = crate::localnet::journal::DirectoryJournal::new(
                &target_reservation.journal_directory,
                Duration::from_secs(2),
            )
            .map_err(|_| INVALID_ARGUMENT)?;
            block_on(
                target_reservation
                    .target
                    .recover_client(&store, attempt_id, descriptor, context),
            )
            .map_err(|_| INVALID_RESPONSE)?
        };
        let client_token = registration.commit(
            client.into_driver(),
            target,
            Arc::clone(&target_reservation.target),
            false,
        )?;
        unsafe { out_client.write(client_token) };
        Ok(())
    })
}

#[cfg(not(feature = "localnet"))]
#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub unsafe extern "C" fn noctium_native_contract_call_recover(
    _target: u64,
    _call_attempt_id: *const u8,
    _call_attempt_id_len: usize,
    _client_descriptor: *const u8,
    _client_descriptor_len: usize,
    _host_context: *const u8,
    _host_context_len: usize,
    out_client: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_client)? };
        Err(INVALID_STATE)
    })
}

#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub extern "C" fn noctium_native_contract_target_free(target: u64) -> i32 {
    guard(|| {
        registry(|r| {
            if r.contract_targets.get(&target).ok_or(INVALID_HANDLE)?.busy {
                return Err(INVALID_STATE);
            }
            r.contract_targets.remove(&target).ok_or(INVALID_HANDLE)?;
            Ok(())
        })
    })
}

#[cfg_attr(not(target_family = "wasm"), unsafe(no_mangle))]
pub extern "C" fn noctium_native_contract_state_free(state: u64) -> i32 {
    guard(|| {
        registry(|r| {
            if r.contract_states.get(&state).ok_or(INVALID_HANDLE)?.busy {
                return Err(INVALID_STATE);
            }
            r.contract_states.remove(&state).ok_or(INVALID_HANDLE)?;
            Ok(())
        })
    })
}
