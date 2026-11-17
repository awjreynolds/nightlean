//! Native proof ABI phase A. Owned tokens only, no retained foreign callback or future.
//! Funding, signing, submission and durable journals are outside this interface.
use crate::{
    artifacts,
    proof::{PreparedProof, TrustedParameters},
};
use futures::executor::block_on;
use rand::{SeedableRng, rngs::StdRng};
use serde::Deserialize;
use serde_json::json;
use std::{
    collections::BTreeMap,
    panic::{AssertUnwindSafe, catch_unwind},
    path::PathBuf,
    sync::{Arc, Mutex, OnceLock},
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
}
struct Private {
    bytes: Zeroizing<Vec<u8>>,
    owner: u64,
}
struct Registry {
    next: u64,
    sessions: BTreeMap<u64, Session>,
    results: BTreeMap<u64, Vec<u8>>,
    private: BTreeMap<u64, Private>,
    active_work: usize,
}
impl Default for Registry {
    fn default() -> Self {
        Self {
            next: 1 << 62,
            sessions: BTreeMap::new(),
            results: BTreeMap::new(),
            private: BTreeMap::new(),
            active_work: 0,
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
}
// Work outlives cancellation of its session. Its resource slot ends only when the call returns.
struct Work;
impl Work {
    fn reserve() -> Result<Self, i32> {
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
fn guard(f: impl FnOnce() -> Result<(), i32>) -> i32 {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(Ok(())) => OK,
        Ok(Err(code)) => code,
        Err(_) => INTERNAL,
    }
}
unsafe fn output(pointer: *mut u64) -> Result<(), i32> {
    if pointer.is_null() {
        return Err(INVALID_ARGUMENT);
    }
    unsafe {
        pointer.write(0);
    }
    Ok(())
}
unsafe fn input<'a>(pointer: *const u8, length: usize, max: usize) -> Result<&'a [u8], i32> {
    if pointer.is_null() || length == 0 {
        return Err(INVALID_ARGUMENT);
    }
    if length > max || length > isize::MAX as usize {
        return Err(LIMIT);
    }
    Ok(unsafe { std::slice::from_raw_parts(pointer, length) })
}
unsafe fn entropy(pointer: *const u8, length: usize) -> Result<StdRng, i32> {
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

/// # Safety
/// Every pointer must reference the stated readable/writable memory until return. Entropy is 32 fresh secret bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_native_begin(
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
            if r.sessions.len() >= MAX_SESSIONS {
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
        registry(|r| {
            if r.sessions.len() >= MAX_SESSIONS {
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
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_native_advance(session: u64, out_result: *mut u64) -> i32 {
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
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_native_private_request(
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
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_native_resume(
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
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_native_local_prove(
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
#[unsafe(no_mangle)]
pub extern "C" fn nightlean_native_cancel(session: u64) -> i32 {
    guard(|| {
        registry(|r| {
            let s = r.sessions.get_mut(&session).ok_or(INVALID_HANDLE)?;
            pending(s)?;
            s.phase = Phase::Cancelled;
            s.payload.zeroize();
            s.prepared = None;
            s.parameters = None;
            r.revoke_private(session);
            Ok(())
        })
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn nightlean_native_free(session: u64) -> i32 {
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
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $len(token: u64, out: *mut usize) -> i32 {
            unsafe { length(token, out, $private) }
        }
        /// # Safety
        /// buffer must reference capacity writable bytes and written a writable size_t.
        #[unsafe(no_mangle)]
        pub unsafe extern "C" fn $copy(
            token: u64,
            buffer: *mut u8,
            capacity: usize,
            written: *mut usize,
        ) -> i32 {
            unsafe { copy(token, buffer, capacity, written, $private) }
        }
        #[unsafe(no_mangle)]
        pub extern "C" fn $free(token: u64) -> i32 {
            free(token, $private)
        }
    };
}
buffers!(
    nightlean_native_result_length,
    nightlean_native_result_copy,
    nightlean_native_result_free,
    false
);
buffers!(
    nightlean_native_private_length,
    nightlean_native_private_copy,
    nightlean_native_private_free,
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
                    },
                );
            }
            Ok((a, b))
        })
        .unwrap();
        assert_eq!(nightlean_native_cancel(a), OK);
        assert_eq!(nightlean_native_free(a), OK);
        assert_eq!(nightlean_native_free(b), OK);
        assert!(matches!(Work::reserve(), Err(LIMIT)));
        drop(first);
        let replacement = Work::reserve().unwrap();
        assert!(matches!(Work::reserve(), Err(LIMIT)));
        drop(second);
        drop(replacement);
        assert_eq!(registry(|r| Ok(r.active_work)), Ok(0));
    }
}
