//! Separate host-control C ABI. No native artifact, proof, signing or commit handle is accepted.
//! Ordinary status/request data belongs to the invocation controller and may reveal private
//! scheduling. It is not a contract log. DF-00 covers successful scalar return payloads only.
use crate::{
    control::{MAX_BYTES, Response, Session},
    host,
};
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    panic::{AssertUnwindSafe, catch_unwind},
    sync::{Mutex, OnceLock},
};
use zeroize::Zeroize;

pub const OK: i32 = 0;
pub const INVALID_ARGUMENT: i32 = 1;
pub const INVALID_HANDLE: i32 = 2;
pub const INVALID_STATE: i32 = 3;
pub const INVALID_RESPONSE: i32 = 4;
pub const LIMIT: i32 = 5;
pub const INTERNAL: i32 = 6;
pub const BUFFER_TOO_SMALL: i32 = 7;
const MAX_SESSIONS: usize = 64;
const MAX_RESULTS: usize = 256;
const MAX_PRIVATE_RESULTS: usize = 64;
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Begin {
    abi_version: u32,
    plan: Json,
    inputs: BTreeMap<String, Json>,
    host_context: host::Context,
}
struct Bytes {
    bytes: Vec<u8>,
    private: bool,
}
impl Drop for Bytes {
    fn drop(&mut self) {
        if self.private {
            self.bytes.zeroize();
        }
    }
}
struct Registry {
    next: u64,
    sessions: BTreeMap<u64, Session>,
    results: BTreeMap<u64, Bytes>,
}
impl Default for Registry {
    fn default() -> Self {
        Self {
            next: 1 << 63,
            sessions: BTreeMap::new(),
            results: BTreeMap::new(),
        }
    }
}
static REGISTRY: OnceLock<Mutex<Registry>> = OnceLock::new();
fn with_registry<T>(f: impl FnOnce(&mut Registry) -> Result<T, i32>) -> Result<T, i32> {
    let mut r = REGISTRY
        .get_or_init(|| Mutex::new(Registry::default()))
        .lock()
        .map_err(|_| INTERNAL)?;
    f(&mut r)
}
impl Registry {
    fn token(&mut self) -> Result<u64, i32> {
        self.next = self.next.checked_add(1).ok_or(LIMIT)?;
        Ok(self.next)
    }
    fn result(&mut self, mut value: Json, private: bool) -> Result<u64, i32> {
        if private && self.results.values().filter(|b| b.private).count() >= MAX_PRIVATE_RESULTS {
            crate::control::wipe_json(&mut value);
            return Err(LIMIT);
        }
        if self.results.len() >= MAX_RESULTS {
            if private {
                crate::control::wipe_json(&mut value);
            }
            return Err(LIMIT);
        }
        let encoded = serde_json::to_vec(&value);
        if private {
            crate::control::wipe_json(&mut value);
        }
        let mut bytes = encoded.map_err(|_| INTERNAL)?;
        if bytes.len() > MAX_BYTES {
            if private {
                bytes.zeroize();
            }
            return Err(LIMIT);
        }
        let bytes = Bytes { bytes, private };
        let token = self.token()?;
        self.results.insert(token, bytes);
        Ok(token)
    }
}
fn guard(f: impl FnOnce() -> Result<(), i32>) -> i32 {
    match catch_unwind(AssertUnwindSafe(f)) {
        Ok(Ok(())) => OK,
        Ok(Err(c)) => c,
        Err(_) => INTERNAL,
    }
}
unsafe fn output(pointer: *mut u64) -> Result<(), i32> {
    if pointer.is_null() {
        return Err(INVALID_ARGUMENT);
    }
    unsafe { pointer.write(0) }
    Ok(())
}
unsafe fn input<'a>(pointer: *const u8, length: usize) -> Result<&'a [u8], i32> {
    if pointer.is_null() || length == 0 {
        return Err(INVALID_ARGUMENT);
    }
    if length > MAX_BYTES {
        return Err(LIMIT);
    }
    Ok(unsafe { std::slice::from_raw_parts(pointer, length) })
}

/// # Safety
/// Input must reference length readable bytes. Output must reference a writable uint64_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_control_begin(
    bytes: *const u8,
    length: usize,
    out_session: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_session)? };
        let bytes = unsafe { input(bytes, length)? };
        let begin: Begin = serde_json::from_slice(bytes).map_err(|_| INVALID_ARGUMENT)?;
        if begin.abi_version != 1 {
            return Err(INVALID_ARGUMENT);
        }
        let session = Session::from_json(begin.plan, begin.inputs, begin.host_context)
            .map_err(|_| INVALID_ARGUMENT)?;
        with_registry(|r| {
            if r.sessions.len() >= MAX_SESSIONS {
                return Err(LIMIT);
            }
            let token = r.token()?;
            r.sessions.insert(token, session);
            unsafe { out_session.write(token) };
            Ok(())
        })
    })
}
fn action(
    session: u64,
    out_result: *mut u64,
    operation: impl FnOnce(&mut Session) -> Result<Json, i32>,
    private: bool,
) -> i32 {
    guard(|| {
        unsafe { output(out_result)? };
        with_registry(|r| {
            if r.results.len() >= MAX_RESULTS {
                return Err(LIMIT);
            }
            let value = operation(r.sessions.get_mut(&session).ok_or(INVALID_HANDLE)?)?;
            let token = r.result(value, private)?;
            unsafe { out_result.write(token) };
            Ok(())
        })
    })
}
/// # Safety
/// out_result must reference a writable uint64_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_control_advance(session: u64, out_result: *mut u64) -> i32 {
    action(
        session,
        out_result,
        |s| s.advance().map_err(|_| INVALID_STATE),
        false,
    )
}
/// # Safety
/// Input and output pointers must satisfy the declared readable/writable lengths.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_control_resume(
    session: u64,
    bytes: *const u8,
    length: usize,
    out_result: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_result)? };
        let response: Response = serde_json::from_slice(unsafe { input(bytes, length)? })
            .map_err(|_| INVALID_RESPONSE)?;
        with_registry(|r| {
            if r.results.len() >= MAX_RESULTS {
                return Err(LIMIT);
            }
            let value = r
                .sessions
                .get_mut(&session)
                .ok_or(INVALID_HANDLE)?
                .resume(response)
                .map_err(|_| INVALID_RESPONSE)?;
            let token = r.result(value, false)?;
            unsafe { out_result.write(token) };
            Ok(())
        })
    })
}
/// # Safety
/// Input and output pointers must satisfy the declared readable/writable lengths.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_control_stage(
    session: u64,
    bytes: *const u8,
    length: usize,
    out_result: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_result)? };
        let stage: host::Stage = serde_json::from_slice(unsafe { input(bytes, length)? })
            .map_err(|_| INVALID_ARGUMENT)?;
        with_registry(|r| {
            if r.results.len() >= MAX_RESULTS {
                return Err(LIMIT);
            }
            r.sessions
                .get_mut(&session)
                .ok_or(INVALID_HANDLE)?
                .stage(stage)
                .map_err(|_| INVALID_RESPONSE)?;
            let token = r.result(json!({"abiVersion":1,"status":"ready"}), false)?;
            unsafe { out_result.write(token) };
            Ok(())
        })
    })
}
/// # Safety
/// out_result must reference a writable uint64_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_control_cancel(session: u64, out_result: *mut u64) -> i32 {
    action(
        session,
        out_result,
        |s| s.cancel().map_err(|_| INVALID_STATE),
        false,
    )
}
#[unsafe(no_mangle)]
pub extern "C" fn nightlean_control_free(session: u64) -> i32 {
    guard(|| {
        with_registry(|r| {
            r.sessions
                .remove(&session)
                .map(|_| ())
                .ok_or(INVALID_HANDLE)
        })
    })
}
/// # Safety
/// out_result must reference a writable uint64_t. The returned token is private.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_control_private_request(
    session: u64,
    out_result: *mut u64,
) -> i32 {
    action(
        session,
        out_result,
        |s| s.private_request().map_err(|_| INVALID_STATE),
        true,
    )
}
/// # Safety
/// out_result must reference a writable uint64_t. The returned token is private.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_control_private_trace(
    session: u64,
    out_result: *mut u64,
) -> i32 {
    action(session, out_result, |s| Ok(s.private_trace()), true)
}
unsafe fn length(token: u64, out_length: *mut usize, private: bool) -> i32 {
    guard(|| {
        if out_length.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        unsafe { out_length.write(0) };
        with_registry(|r| {
            let b = r
                .results
                .get(&token)
                .filter(|b| b.private == private)
                .ok_or(INVALID_HANDLE)?;
            unsafe { out_length.write(b.bytes.len()) };
            Ok(())
        })
    })
}
unsafe fn copy(
    token: u64,
    buffer: *mut u8,
    capacity: usize,
    out_written: *mut usize,
    private: bool,
) -> i32 {
    guard(|| {
        if out_written.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        unsafe { out_written.write(0) };
        if buffer.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        with_registry(|r| {
            let b = r
                .results
                .get(&token)
                .filter(|b| b.private == private)
                .ok_or(INVALID_HANDLE)?;
            if capacity < b.bytes.len() {
                return Err(BUFFER_TOO_SMALL);
            }
            unsafe {
                std::ptr::copy_nonoverlapping(b.bytes.as_ptr(), buffer, b.bytes.len());
                out_written.write(b.bytes.len())
            };
            Ok(())
        })
    })
}
fn free(token: u64, private: bool) -> i32 {
    guard(|| {
        with_registry(|r| {
            if r.results.get(&token).is_none_or(|b| b.private != private) {
                return Err(INVALID_HANDLE);
            }
            r.results.remove(&token);
            Ok(())
        })
    })
}
/// # Safety
/// out_length must reference a writable size_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_control_result_length(
    token: u64,
    out_length: *mut usize,
) -> i32 {
    unsafe { length(token, out_length, false) }
}
/// # Safety
/// buffer must reference capacity writable bytes. out_written must reference a writable size_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_control_result_copy(
    token: u64,
    buffer: *mut u8,
    capacity: usize,
    out_written: *mut usize,
) -> i32 {
    unsafe { copy(token, buffer, capacity, out_written, false) }
}
#[unsafe(no_mangle)]
pub extern "C" fn nightlean_control_result_free(token: u64) -> i32 {
    free(token, false)
}
/// # Safety
/// out_length must reference a writable size_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_control_private_length(
    token: u64,
    out_length: *mut usize,
) -> i32 {
    unsafe { length(token, out_length, true) }
}
/// # Safety
/// buffer must reference capacity writable bytes. out_written must reference a writable size_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_control_private_copy(
    token: u64,
    buffer: *mut u8,
    capacity: usize,
    out_written: *mut usize,
) -> i32 {
    unsafe { copy(token, buffer, capacity, out_written, true) }
}
#[unsafe(no_mangle)]
pub extern "C" fn nightlean_control_private_free(token: u64) -> i32 {
    free(token, true)
}
