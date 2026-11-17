//! Explicit development-host capability adapter. No default endpoint, seed or filesystem path.
use crate::{
    client::{ChainAdapter, FundingAdapter, JournalStore, NetworkPolicy, SigningAdapter},
    funding::FeePolicy,
    localnet::{DevelopmentFunding, ExplicitSeal, Node, ProofCache, journal::DirectoryJournal},
    native_client::{Capabilities, RequestData, ServiceReply},
    native_ffi::{
        self as ffi, INTERNAL, INVALID_ARGUMENT, INVALID_HANDLE, INVALID_STATE, LIMIT, Work,
    },
};
use futures::executor::block_on;
use serde::Deserialize;
use serde_json::json;
use std::{
    collections::BTreeMap,
    path::PathBuf,
    sync::{Arc, Mutex, OnceLock},
    time::Duration,
};
const DEVELOPMENT_GENESIS: &str =
    "823383ec0302be8417cfcbcc62f21df08f4047bca37aaea89e3f54b550ebae1d";
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Configuration {
    abi_version: u32,
    #[serde(deserialize_with = "crate::native_client::policy")]
    policy: NetworkPolicy,
    capabilities: Capabilities,
    endpoint: String,
    timeout_millis: u32,
    max_response_bytes: u32,
    max_replay_blocks: String,
    journal_directory: PathBuf,
    parameter_cache: Option<PathBuf>,
    parameter_source: Option<String>,
    dust_srs_sha256: Option<String>,
    public_development_genesis: bool,
}
struct Services {
    node: Node,
    store: DirectoryJournal,
    policy: NetworkPolicy,
    capabilities: Capabilities,
    material: Option<(
        crate::funding::DustMaterial,
        crate::proof::TrustedParameters,
    )>,
}
struct Registry {
    next: u64,
    services: BTreeMap<u64, Arc<Mutex<Services>>>,
}
static REGISTRY: OnceLock<Mutex<Registry>> = OnceLock::new();
fn registry<T>(f: impl FnOnce(&mut Registry) -> Result<T, i32>) -> Result<T, i32> {
    let mut r = REGISTRY
        .get_or_init(|| {
            Mutex::new(Registry {
                next: 1 << 61,
                services: BTreeMap::new(),
            })
        })
        .lock()
        .map_err(|_| INTERNAL)?;
    f(&mut r)
}
fn services(token: u64) -> Result<Arc<Mutex<Services>>, i32> {
    registry(|r| r.services.get(&token).cloned().ok_or(INVALID_HANDLE))
}
/// # Safety
/// Public config/private seed/output buffers must remain valid until return. Seed is optional for recovery.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_localnet_open(
    config: *const u8,
    config_len: usize,
    seed: *const u8,
    seed_len: usize,
    out_adapter: *mut u64,
) -> i32 {
    ffi::guard(|| {
        unsafe { ffi::output(out_adapter)? };
        let config: Configuration =
            serde_json::from_slice(unsafe { ffi::input(config, config_len, 65536)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        let replay = config
            .max_replay_blocks
            .parse::<u64>()
            .ok()
            .filter(|v| v.to_string() == config.max_replay_blocks)
            .ok_or(INVALID_ARGUMENT)?;
        if config.abi_version != 1
            || !config.public_development_genesis
            || config.policy.genesis != DEVELOPMENT_GENESIS
            || !config.capabilities.validate()
        {
            return Err(INVALID_ARGUMENT);
        }
        let _work = Work::reserve()?;
        registry(|r| {
            if r.services.len() >= 2 {
                Err(LIMIT)
            } else {
                Ok(())
            }
        })?;
        let node = Node::connect(
            &config.endpoint,
            config.policy.clone(),
            Duration::from_millis(config.timeout_millis.into()),
            config.max_response_bytes as usize,
            replay,
        )
        .map_err(|_| INVALID_ARGUMENT)?;
        let material = if let Some(directory) = config.parameter_cache {
            let source = config
                .parameter_source
                .as_ref()
                .ok_or(INVALID_ARGUMENT)?
                .parse()
                .map_err(|_| INVALID_ARGUMENT)?;
            let cache = ProofCache::new(directory, source).map_err(|_| INVALID_ARGUMENT)?;
            let material = block_on(cache.dust()).map_err(|_| INVALID_ARGUMENT)?;
            let parameters =
                block_on(cache.parameters(material.k())).map_err(|_| INVALID_ARGUMENT)?;
            if Some(parameters.sha256()) != config.dust_srs_sha256.as_deref() {
                return Err(INVALID_ARGUMENT);
            }
            Some((material, parameters))
        } else {
            if config.parameter_source.is_some() || config.dust_srs_sha256.is_some() {
                return Err(INVALID_ARGUMENT);
            }
            None
        };
        let store = DirectoryJournal::new(&config.journal_directory, Duration::from_secs(2))
            .map_err(|_| INVALID_ARGUMENT)?;
        if seed_len != 0 {
            if material.is_none() || !matches!(seed_len, 16 | 32) {
                return Err(INVALID_ARGUMENT);
            }
            node.attach_dust_seed(unsafe { ffi::input(seed, seed_len, 32)? })
                .map_err(|_| INVALID_ARGUMENT)?;
        }
        let service = Services {
            node,
            store,
            policy: config.policy,
            capabilities: config.capabilities,
            material,
        };
        registry(|r| {
            if r.services.len() >= 2 {
                return Err(LIMIT);
            }
            r.next = r
                .next
                .checked_add(1)
                .filter(|n| *n < 1 << 62)
                .ok_or(LIMIT)?;
            let token = r.next;
            r.services.insert(token, Arc::new(Mutex::new(service)));
            unsafe { out_adapter.write(token) }
            Ok(())
        })
    })
}
/// # Safety
/// out_result must reference writable memory. Returns public context for explicit TTL selection.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_localnet_context(adapter: u64, out_result: *mut u64) -> i32 {
    ffi::guard(|| {
        unsafe { ffi::output(out_result)? };
        let _work = Work::reserve()?;
        let service = services(adapter)?;
        let s = service.lock().map_err(|_| INTERNAL)?;
        let snapshot = s.node.sync().map_err(|_| INVALID_STATE)?;
        let mut parameters = Vec::new();
        serialize::tagged_serialize(&*snapshot.state.parameters, &mut parameters)
            .map_err(|_| INTERNAL)?;
        let bytes=serde_json::to_vec(&json!({"abiVersion":1,"profile":crate::profile::NAME,"networkId":snapshot.chain.network_id,"genesis":snapshot.chain.genesis,"height":snapshot.height.to_string(),"finalizedHash":snapshot.finalized_hash,"blockTime":snapshot.block.tblock.to_secs().to_string(),"ledgerParametersSha256":crate::artifacts::digest(&parameters)})).map_err(|_|INTERNAL)?;
        let token = ffi::service_public_bytes(bytes)?;
        unsafe { out_result.write(token) }
        Ok(())
    })
}
/// # Safety
/// Explicit entropy/output buffers must remain valid until return. Entropy is required only for funding/signing.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_localnet_resolve(
    adapter: u64,
    request: u64,
    approve: u32,
    coins: *const u8,
    coins_len: usize,
    out_reply: *mut u64,
) -> i32 {
    ffi::guard(|| {
        unsafe { ffi::output(out_reply)? };
        if approve > 1 {
            return Err(INVALID_ARGUMENT);
        }
        let _work = Work::reserve()?;
        let q = ffi::service_request(request)?;
        let service = services(adapter)?;
        let s = service.lock().map_err(|_| INTERNAL)?;
        let expected = match &q.request.data {
            RequestData::Snapshot | RequestData::Submit(_) | RequestData::Observe(_) => {
                &s.capabilities.chain
            }
            RequestData::Fund { .. } => &s.capabilities.funding,
            RequestData::Sign { .. } => &s.capabilities.signing,
            _ => &s.capabilities.journal,
        };
        if q.request.capability != *expected || q.request.policy != s.policy {
            return Err(INVALID_ARGUMENT);
        }
        let value = match &q.request.data {
            RequestData::Snapshot => block_on(s.node.snapshot()).map(ServiceReply::Snapshot),
            RequestData::Submit(t) => block_on(s.node.submit(t)).map(ServiceReply::Submitted),
            RequestData::Observe(t) => block_on(s.node.observe(t)).map(ServiceReply::Observed),
            RequestData::Fund { contract, snapshot } => {
                let Some((material, parameters)) = &s.material else {
                    return Err(INVALID_STATE);
                };
                s.policy
                    .check(&snapshot.chain)
                    .map_err(|_| INVALID_ARGUMENT)?;
                let rng = unsafe { ffi::entropy(coins, coins_len)? };
                block_on(
                    DevelopmentFunding::new(
                        &s.node,
                        material,
                        parameters,
                        FeePolicy {
                            max_dust: s.policy.max_dust,
                            margin_blocks: 3,
                            max_spends: 8,
                        },
                        rng,
                    )
                    .fund(contract, snapshot, &s.policy),
                )
                .map(ServiceReply::Funded)
            }
            RequestData::Sign {
                transaction,
                snapshot,
            } => {
                s.policy
                    .check(&snapshot.chain)
                    .map_err(|_| INVALID_ARGUMENT)?;
                if approve == 0 {
                    Err(crate::client::HostFailure)
                } else {
                    let rng = unsafe { ffi::entropy(coins, coins_len)? };
                    block_on(
                        ExplicitSeal::new(
                            |_: &crate::funding::UnsealedTransaction, p: &NetworkPolicy| {
                                *p == s.policy
                            },
                            rng,
                        )
                        .approve_and_sign(transaction, snapshot, &s.policy),
                    )
                    .map(ServiceReply::Signed)
                }
            }
            RequestData::Load(id) => block_on(s.store.load(id)).map(ServiceReply::Loaded),
            RequestData::Persist {
                record,
                expected_revision,
            } => block_on(s.store.persist(record, *expected_revision)).map(ServiceReply::Persisted),
            RequestData::Cas(record) => {
                block_on(s.store.compare_exchange(record)).map(ServiceReply::Cas)
            }
        }
        .unwrap_or(ServiceReply::Failure);
        drop(s);
        let token = ffi::service_reply(request, value)?;
        unsafe { out_reply.write(token) }
        Ok(())
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn nightlean_localnet_free(adapter: u64) -> i32 {
    ffi::guard(|| {
        registry(|r| {
            r.services.remove(&adapter).ok_or(INVALID_HANDLE)?;
            ffi::service_private_revoke(adapter);
            Ok(())
        })
    })
}
/// # Safety
/// Request and writable output pointers must remain valid until return. Result token is private.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_localnet_private_value(
    adapter: u64,
    request: *const u8,
    request_len: usize,
    out_private: *mut u64,
) -> i32 {
    #[derive(Deserialize)]
    #[serde(deny_unknown_fields)]
    struct Read {
        namespace: String,
        key: String,
    }
    ffi::guard(|| {
        unsafe { ffi::output(out_private)? };
        let r: Read = serde_json::from_slice(unsafe { ffi::input(request, request_len, 65536)? })
            .map_err(|_| INVALID_ARGUMENT)?;
        if r.namespace.len() > 128 || r.key.len() > 128 {
            return Err(INVALID_ARGUMENT);
        }
        let _work = Work::reserve()?;
        let service = services(adapter)?;
        let s = service.lock().map_err(|_| INTERNAL)?;
        let value = s
            .store
            .private_value(&r.namespace, &r.key)
            .map_err(|_| INVALID_STATE)?;
        let bytes = zeroize::Zeroizing::new(serde_json::to_vec(&value).map_err(|_| INTERNAL)?);
        let token = ffi::service_private_bytes(adapter, bytes)?;
        unsafe { out_private.write(token) }
        Ok(())
    })
}
