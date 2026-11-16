//! C ABI v1: opaque integer tokens and caller-owned copy buffers.
//!
//! Pointer arguments follow the C contract in include/nightlean_runtime.h. The
//! runtime validates nulls/lengths, but a foreign caller must provide readable
//! input memory and writable output memory. Invalid raw addresses are not
//! recoverable by Rust panic handling.
use crate::zkir::IrSource;
use crate::{Plan, ScalarType, check, create_state, environment, input_value, prepare};
use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use ledger::structure::LedgerParameters;
use serde::Deserialize;
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    panic::{AssertUnwindSafe, catch_unwind},
    ptr, slice,
    sync::{Mutex, OnceLock},
};
use zeroize::Zeroize;

pub const ABI_VERSION: u32 = 1;
pub const OK: i32 = 0;
pub const INVALID_ARGUMENT: i32 = 1;
pub const INVALID_HANDLE: i32 = 2;
pub const INVALID_STATE: i32 = 3;
pub const INVALID_RESPONSE: i32 = 4;
pub const LIMIT: i32 = 5;
pub const INTERNAL: i32 = 6;
pub const BUFFER_TOO_SMALL: i32 = 7;
pub const MAX_INPUT_BYTES: usize = 1_048_576;
pub const MAX_SESSIONS: usize = 64;
pub const MAX_RESULTS: usize = 256;
const MAX_OPERATIONS: usize = 4096;
const MAX_INPUTS: usize = 256;
const PROFILE: &str = crate::profile::ABI;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Begin {
    abi_version: u32,
    profile: String,
    plan: Plan,
    public_inputs: BTreeMap<String, Json>,
    state: BTreeMap<String, Json>,
    ledger_parameters_hex: String,
    address: String,
    circuit: Json,
    #[serde(default)]
    host_context: Option<crate::host::Context>,
}
#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Response {
    abi_version: u32,
    request_id: u64,
    value: Json,
    #[serde(default)]
    operation: Option<String>,
    #[serde(default)]
    capability: Option<String>,
    #[serde(default)]
    schema: Option<String>,
}
#[derive(Clone)]
enum Phase {
    Ready,
    Waiting { index: usize, id: u64 },
    Running,
    Complete(Json),
    Failed,
    Cancelled,
}
struct Session {
    plan: Plan,
    inputs: BTreeMap<String, Json>,
    state: BTreeMap<String, Json>,
    parameters: Vec<u8>,
    address: [u8; 32],
    circuit: Vec<u8>,
    phase: Phase,
    next_request: u64,
    host: Option<crate::host::Runtime>,
}
fn wipe_json(value: &mut Json) {
    match value {
        Json::String(s) => s.zeroize(),
        Json::Array(a) => a.iter_mut().for_each(wipe_json),
        Json::Object(o) => o.values_mut().for_each(wipe_json),
        _ => {}
    }
}
impl Drop for Session {
    fn drop(&mut self) {
        self.inputs.values_mut().for_each(wipe_json);
        self.state.values_mut().for_each(wipe_json);
    }
}
#[derive(Default)]
struct Registry {
    next: u64,
    sessions: BTreeMap<u64, Session>,
    results: BTreeMap<u64, Vec<u8>>,
    private_results: BTreeMap<u64, Vec<u8>>,
}
static REGISTRY: OnceLock<Mutex<Registry>> = OnceLock::new();
fn registry() -> std::sync::MutexGuard<'static, Registry> {
    REGISTRY
        .get_or_init(|| Mutex::new(Registry::default()))
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner())
}
impl Registry {
    fn token(&mut self) -> Result<u64, i32> {
        self.next = self.next.checked_add(1).ok_or(LIMIT)?;
        Ok(self.next)
    }
    fn result(&mut self, value: Json) -> Result<u64, i32> {
        if self.results.len() >= MAX_RESULTS {
            return Err(LIMIT);
        }
        let bytes = serde_json::to_vec(&value).map_err(|_| INTERNAL)?;
        if bytes.len() > MAX_INPUT_BYTES {
            return Err(LIMIT);
        }
        let token = self.token()?;
        self.results.insert(token, bytes);
        Ok(token)
    }
}
fn status(name: &str) -> Json {
    json!({"abiVersion":ABI_VERSION,"status":name})
}
fn guard(operation: impl FnOnce() -> Result<(), i32>) -> i32 {
    match catch_unwind(AssertUnwindSafe(operation)) {
        Ok(Ok(())) => OK,
        Ok(Err(code)) => code,
        Err(_) => INTERNAL,
    }
}
unsafe fn output(pointer: *mut u64) -> Result<(), i32> {
    if pointer.is_null() {
        return Err(INVALID_ARGUMENT);
    }
    unsafe { pointer.write(0) };
    Ok(())
}
unsafe fn input<'a>(pointer: *const u8, length: usize) -> Result<&'a [u8], i32> {
    if length == 0 || length > MAX_INPUT_BYTES || length > isize::MAX as usize || pointer.is_null()
    {
        return Err(INVALID_ARGUMENT);
    }
    Ok(unsafe { slice::from_raw_parts(pointer, length) })
}
fn validate_circuit(value: &Json) -> Result<(), i32> {
    if value.get("version") != Some(&json!({"major":3,"minor":2}))
        || value.get("do_communications_commitment") != Some(&Json::Bool(true))
    {
        return Err(INVALID_ARGUMENT);
    }
    if !value
        .get("inputs")
        .and_then(Json::as_array)
        .is_some_and(|a| a.is_empty())
        || !value
            .get("outputs")
            .and_then(Json::as_array)
            .is_some_and(|a| a.is_empty())
    {
        return Err(INVALID_ARGUMENT);
    }
    let instructions = value
        .get("instructions")
        .and_then(Json::as_array)
        .ok_or(INVALID_ARGUMENT)?;
    if instructions.len() > MAX_OPERATIONS {
        return Err(LIMIT);
    }
    for instruction in instructions {
        let operation = instruction
            .get("op")
            .and_then(Json::as_str)
            .ok_or(INVALID_ARGUMENT)?;
        if !matches!(
            operation,
            "public_input"
                | "private_input"
                | "constrain_to_boolean"
                | "add"
                | "mul"
                | "test_eq"
                | "cond_select"
                | "transient_hash"
                | "assert"
                | "impact"
                | "output"
                | "neg"
                | "not"
                | "constrain_eq"
                | "constrain_bits"
                | "less_than"
        ) {
            return Err(INVALID_ARGUMENT);
        }
        if matches!(operation, "constrain_bits" | "less_than")
            && !instruction
                .get("bits")
                .and_then(Json::as_u64)
                .is_some_and(|bits| bits > 0 && bits <= crate::MAX_UINT_BITS as u64)
        {
            return Err(INVALID_ARGUMENT);
        }
        if let Some(inputs) = instruction.get("inputs").and_then(Json::as_array) {
            if inputs.len() > MAX_INPUTS {
                return Err(LIMIT);
            }
        }
    }
    Ok(())
}
fn validate_begin(begin: Begin) -> Result<Session, i32> {
    if begin.abi_version != ABI_VERSION
        || begin.profile != PROFILE
        || begin.plan.schema_version != 1
        || !crate::profile::validate_plan(
            begin.plan.target.as_deref(),
            begin.plan.target_profile.as_ref(),
        )
    {
        return Err(INVALID_ARGUMENT);
    }
    let plan = &begin.plan;
    if plan.circuit.inputs.len() > MAX_INPUTS
        || plan.circuit.outputs.len() > MAX_INPUTS
        || plan.operations.len() > MAX_OPERATIONS
        || plan.reads.len() > MAX_INPUTS
        || plan.state.len() > 16
    {
        return Err(LIMIT);
    }
    let mut names = std::collections::BTreeSet::new();
    for input in &plan.circuit.inputs {
        if input.name.len() > 128
            || !names.insert(input.name.clone())
            || ScalarType::parse(&input.ty).is_err()
            || !matches!(input.visibility.as_str(), "public" | "private")
        {
            return Err(INVALID_ARGUMENT);
        }
        if input.visibility == "public" {
            let value = begin
                .public_inputs
                .get(&input.name)
                .ok_or(INVALID_ARGUMENT)?;
            input_value(&input.ty, value).map_err(|_| INVALID_ARGUMENT)?;
        } else if begin.public_inputs.contains_key(&input.name) {
            return Err(INVALID_ARGUMENT);
        }
    }
    if begin.public_inputs.len()
        != plan
            .circuit
            .inputs
            .iter()
            .filter(|input| input.visibility == "public")
            .count()
    {
        return Err(INVALID_ARGUMENT);
    }
    for output in &plan.circuit.outputs {
        if output.visibility != "public"
            || output.name.len() > 128
            || !names.insert(output.name.clone())
            || ScalarType::parse(&output.ty).is_err()
        {
            return Err(INVALID_ARGUMENT);
        }
    }
    let parameters = hex::decode(&begin.ledger_parameters_hex).map_err(|_| INVALID_ARGUMENT)?;
    let _: LedgerParameters =
        serialize::tagged_deserialize(parameters.as_slice()).map_err(|_| INVALID_ARGUMENT)?;
    let address: [u8; 32] = hex::decode(&begin.address)
        .map_err(|_| INVALID_ARGUMENT)?
        .try_into()
        .map_err(|_| INVALID_ARGUMENT)?;
    create_state(plan, &begin.state).map_err(|_| INVALID_ARGUMENT)?;
    validate_circuit(&begin.circuit)?;
    let circuit = serde_json::to_vec(&begin.circuit).map_err(|_| INVALID_ARGUMENT)?;
    IrSource::load(circuit.as_slice()).map_err(|_| INVALID_ARGUMENT)?;
    let private_inputs = plan
        .circuit
        .inputs
        .iter()
        .filter(|i| i.visibility == "private")
        .map(|i| (i.name.clone(), i.ty.clone()))
        .collect();
    let host = begin
        .host_context
        .map(|context| {
            crate::host::Runtime::new(
                context,
                &private_inputs,
                hex::encode(address),
                plan.entrypoint.clone(),
            )
            .map_err(host_error)
        })
        .transpose()?;
    Ok(Session {
        plan: begin.plan,
        inputs: begin.public_inputs,
        state: begin.state,
        parameters,
        address,
        circuit,
        phase: Phase::Ready,
        next_request: 0,
        host,
    })
}
fn complete(session: &Session) -> Result<Json, ()> {
    let parameters: LedgerParameters =
        serialize::tagged_deserialize(session.parameters.as_slice()).map_err(|_| ())?;
    let state = create_state(&session.plan, &session.state).map_err(|_| ())?;
    let execution = prepare(
        &session.plan,
        &session.inputs,
        &state,
        &parameters,
        ContractAddress(HashOutput(session.address)),
    )
    .map_err(|_| ())?;
    let circuit = IrSource::load(session.circuit.as_slice()).map_err(|_| ())?;
    let active = check(&execution, &circuit).map_err(|_| ())?;
    let env = environment(&session.plan, &session.inputs).map_err(|_| ())?;
    let outputs: serde_json::Map<String, Json> = session
        .plan
        .circuit
        .outputs
        .iter()
        .map(|out| {
            let value = env[&out.name].public_json();
            (out.name.clone(), value)
        })
        .collect();
    Ok(
        json!({"abiVersion":ABI_VERSION,"status":"completed","result":{"publicOutputs":outputs,"operations":execution.program.len(),"activityGroups":active.len(),"officialCircuitChecked":true,"proofGenerated":false,"transactionSubmitted":false,"privateStateJournal":null}}),
    )
}
fn host_error(error: crate::host::Error) -> i32 {
    match error {
        crate::host::Error::Descriptor => INVALID_ARGUMENT,
        crate::host::Error::Denied | crate::host::Error::Response => INVALID_RESPONSE,
        crate::host::Error::State => INVALID_STATE,
        crate::host::Error::Limit => LIMIT,
    }
}
fn advance(session: &mut Session) -> Result<Json, i32> {
    if let Some(request) = session.host.as_ref().and_then(|h| h.cas_metadata()) {
        return Ok(json!({"abiVersion":1,"status":"need_host","request":request}));
    }
    match &session.phase {
        Phase::Complete(result) => return Ok(result.clone()),
        Phase::Cancelled => return Ok(status("cancelled")),
        Phase::Failed => {
            return Ok(
                json!({"abiVersion":ABI_VERSION,"status":"failed","error":{"code":"execution_rejected"}}),
            );
        }
        Phase::Running => return Err(INVALID_STATE),
        Phase::Ready | Phase::Waiting { .. } => {}
    }
    let pending = match &session.phase {
        Phase::Waiting { index, id } => Some((*index, *id)),
        _ => session
            .plan
            .circuit
            .inputs
            .iter()
            .enumerate()
            .find(|(_, input)| {
                input.visibility == "private" && !session.inputs.contains_key(&input.name)
            })
            .map(|(index, _)| {
                session.next_request += 1;
                (index, session.next_request)
            }),
    };
    if let Some((index, id)) = pending {
        let input = &session.plan.circuit.inputs[index];
        if !matches!(session.phase, Phase::Waiting { .. }) {
            if let Some(host) = &mut session.host {
                host.begin_input(&input.name, id).map_err(host_error)?;
            }
        }
        session.phase = Phase::Waiting { index, id };
        if let Some(request) = session
            .host
            .as_ref()
            .map(|h| h.input_metadata())
            .transpose()
            .map_err(host_error)?
            .flatten()
        {
            return Ok(json!({"abiVersion":1,"status":"need_host","request":request}));
        }
        return Ok(
            json!({"abiVersion":ABI_VERSION,"status":"need_host","request":{"id":id,"operation":"witness.input","name":input.name,"type":input.ty,"visibility":"private"}}),
        );
    }
    session.phase = Phase::Running;
    match complete(session) {
        Ok(result) => {
            if let Some(host) = &mut session.host {
                host.execution_finished(true).map_err(host_error)?;
            }
            session.phase = Phase::Complete(result.clone());
            session.inputs.values_mut().for_each(wipe_json);
            Ok(result)
        }
        Err(()) => {
            if let Some(host) = &mut session.host {
                host.execution_finished(false).map_err(host_error)?;
            }
            session.phase = Phase::Failed;
            session.inputs.values_mut().for_each(wipe_json);
            Ok(
                json!({"abiVersion":ABI_VERSION,"status":"failed","error":{"code":"execution_rejected"}}),
            )
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn nightlean_runtime_abi_version() -> u32 {
    ABI_VERSION
}

/// # Safety
/// Foreign pointers must satisfy the readable/writable memory contract in the C header.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_session_begin(
    bytes: *const u8,
    length: usize,
    out_session: *mut u64,
    out_result: *mut u64,
) -> i32 {
    guard(|| {
        let session_output = unsafe { output(out_session) };
        let result_output = unsafe { output(out_result) };
        session_output?;
        result_output?;
        let bytes = unsafe { input(bytes, length)? };
        let begin: Begin = serde_json::from_slice(bytes).map_err(|_| INVALID_ARGUMENT)?;
        let session = validate_begin(begin)?;
        let mut registry = registry();
        if registry.sessions.len() >= MAX_SESSIONS {
            return Err(LIMIT);
        }
        let result = registry.result(status("ready"))?;
        let token = registry.token()?;
        registry.sessions.insert(token, session);
        unsafe {
            out_session.write(token);
            out_result.write(result)
        };
        Ok(())
    })
}
/// # Safety
/// out_result must point to writable storage for one uint64_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_session_advance(session: u64, out_result: *mut u64) -> i32 {
    guard(|| {
        unsafe { output(out_result)? };
        let mut registry = registry();
        if registry.results.len() >= MAX_RESULTS {
            return Err(LIMIT);
        }
        let value = advance(registry.sessions.get_mut(&session).ok_or(INVALID_HANDLE)?)?;
        let result = registry.result(value)?;
        unsafe { out_result.write(result) };
        Ok(())
    })
}
/// # Safety
/// bytes/length and out_result must satisfy the C header's memory contract.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_session_resume(
    session: u64,
    bytes: *const u8,
    length: usize,
    out_result: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_result)? };
        let response: Response = serde_json::from_slice(unsafe { input(bytes, length)? })
            .map_err(|_| INVALID_RESPONSE)?;
        let mut registry = registry();
        if registry.results.len() >= MAX_RESULTS {
            return Err(LIMIT);
        }
        let state = registry.sessions.get_mut(&session).ok_or(INVALID_HANDLE)?;
        if state
            .host
            .as_ref()
            .is_some_and(|h| h.cas_metadata().is_some())
        {
            if response.abi_version != ABI_VERSION {
                return Err(INVALID_RESPONSE);
            }
            let host = state.host.as_mut().ok_or(INVALID_STATE)?;
            host.finish_cas(
                response.request_id,
                response.operation.as_deref(),
                response.capability.as_deref(),
                response.schema.as_deref(),
                response.value,
            )
            .map_err(host_error)?;
            let value = host.public_status();
            let result = registry.result(value)?;
            unsafe { out_result.write(result) };
            return Ok(());
        }
        let Phase::Waiting { index, id } = state.phase else {
            return Err(INVALID_STATE);
        };
        if response.abi_version != ABI_VERSION || response.request_id != id {
            return Err(INVALID_RESPONSE);
        }
        let input = &state.plan.circuit.inputs[index];
        input_value(&input.ty, &response.value).map_err(|_| INVALID_RESPONSE)?;
        if let Some(host) = &mut state.host {
            host.finish_input(
                &input.name,
                id,
                response.operation.as_deref(),
                response.capability.as_deref(),
                response.schema.as_deref(),
                &response.value,
            )
            .map_err(host_error)?;
        } else if response.operation.is_some()
            || response.capability.is_some()
            || response.schema.is_some()
        {
            return Err(INVALID_RESPONSE);
        }
        state.inputs.insert(input.name.clone(), response.value);
        state.phase = Phase::Ready;
        let result = registry.result(status("ready"))?;
        unsafe { out_result.write(result) };
        Ok(())
    })
}
/// # Safety
/// out_result must point to writable storage for one uint64_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_session_cancel(session: u64, out_result: *mut u64) -> i32 {
    guard(|| {
        unsafe { output(out_result)? };
        let mut registry = registry();
        if registry.results.len() >= MAX_RESULTS {
            return Err(LIMIT);
        }
        let state = registry.sessions.get_mut(&session).ok_or(INVALID_HANDLE)?;
        if let Some(host) = &mut state.host {
            host.cancel().map_err(host_error)?;
        } else if matches!(state.phase, Phase::Complete(_) | Phase::Failed) {
            return Err(INVALID_STATE);
        }
        state.phase = Phase::Cancelled;
        state.inputs.values_mut().for_each(wipe_json);
        let result = registry.result(status("cancelled"))?;
        unsafe { out_result.write(result) };
        Ok(())
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn nightlean_session_free(session: u64) -> i32 {
    guard(|| {
        registry().sessions.remove(&session).ok_or(INVALID_HANDLE)?;
        Ok(())
    })
}
/// # Safety
/// out_length must point to writable storage for one size_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_result_length(result: u64, out_length: *mut usize) -> i32 {
    guard(|| {
        if out_length.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        unsafe { out_length.write(0) };
        let registry = registry();
        let bytes = registry.results.get(&result).ok_or(INVALID_HANDLE)?;
        unsafe { out_length.write(bytes.len()) };
        Ok(())
    })
}
/// # Safety
/// destination must be writable for capacity bytes; out_written for one size_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_result_copy(
    result: u64,
    destination: *mut u8,
    capacity: usize,
    out_written: *mut usize,
) -> i32 {
    guard(|| {
        if out_written.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        unsafe { out_written.write(0) };
        let registry = registry();
        let bytes = registry.results.get(&result).ok_or(INVALID_HANDLE)?;
        if capacity < bytes.len() {
            return Err(BUFFER_TOO_SMALL);
        }
        if destination.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        unsafe {
            ptr::copy_nonoverlapping(bytes.as_ptr(), destination, bytes.len());
            out_written.write(bytes.len())
        };
        Ok(())
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn nightlean_result_free(result: u64) -> i32 {
    guard(|| {
        let mut bytes = registry().results.remove(&result).ok_or(INVALID_HANDLE)?;
        bytes.zeroize();
        Ok(())
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn unsigned_instruction_limits_are_explicit() {
        let mut circuit = json!({"version":{"major":3,"minor":2},"do_communications_commitment":true,"inputs":[],"outputs":[],"instructions":[]});
        for operation in ["neg", "not", "constrain_eq", "constrain_bits", "less_than"] {
            circuit["instructions"] = json!([{"op":operation,"bits":248}]);
            assert!(validate_circuit(&circuit).is_ok());
        }
        for bits in [json!(0), json!(249), json!("8"), json!(-1), Json::Null] {
            circuit["instructions"] = json!([{"op":"constrain_bits","bits":bits}]);
            assert_eq!(validate_circuit(&circuit), Err(INVALID_ARGUMENT));
        }
        for unsupported in ["sub", "assert_equal", "eval"] {
            circuit["instructions"] = json!([{"op":unsupported}]);
            assert_eq!(validate_circuit(&circuit), Err(INVALID_ARGUMENT));
        }
    }
    #[test]
    fn null_inputs_and_forged_tokens_reject() {
        assert_eq!(nightlean_runtime_abi_version(), 1);
        let mut session = 0;
        let mut result = 0;
        assert_eq!(
            unsafe { nightlean_session_begin(ptr::null(), 1, &mut session, &mut result) },
            INVALID_ARGUMENT
        );
        let one_byte = 0u8;
        assert_eq!(
            unsafe {
                nightlean_session_begin(&one_byte, MAX_INPUT_BYTES + 1, &mut session, &mut result)
            },
            INVALID_ARGUMENT
        );
        assert_eq!(
            unsafe { nightlean_session_advance(u64::MAX, &mut result) },
            INVALID_HANDLE
        );
        assert_eq!(nightlean_session_free(u64::MAX), INVALID_HANDLE);
        assert_eq!(nightlean_result_free(u64::MAX), INVALID_HANDLE);
    }
    #[test]
    fn result_lifetime_and_copy_contract() {
        let result = registry().result(status("ready")).unwrap();
        let mut len = 0;
        assert_eq!(unsafe { nightlean_result_length(result, &mut len) }, OK);
        assert!(len > 0);
        let mut written = 0;
        let mut bytes = vec![0; len];
        assert_eq!(
            unsafe { nightlean_result_copy(result, bytes.as_mut_ptr(), len - 1, &mut written) },
            BUFFER_TOO_SMALL
        );
        assert_eq!(written, 0);
        assert_eq!(
            unsafe { nightlean_result_copy(result, bytes.as_mut_ptr(), len, &mut written) },
            OK
        );
        assert_eq!(written, len);
        assert_eq!(nightlean_result_free(result), OK);
        assert_eq!(nightlean_result_free(result), INVALID_HANDLE);
        assert_eq!(
            unsafe { nightlean_result_length(result, &mut len) },
            INVALID_HANDLE
        );
    }
}

pub const MAX_PRIVATE_RESULTS: usize = 64;
pub const PRIVATE_REQUEST: u32 = 1;
pub const PRIVATE_JOURNAL: u32 = 2;
impl Registry {
    fn private_result(&mut self, mut value: Json) -> Result<u64, i32> {
        if self.private_results.len() >= MAX_PRIVATE_RESULTS {
            wipe_json(&mut value);
            return Err(LIMIT);
        }
        let encoded = serde_json::to_vec(&value).map_err(|_| INTERNAL);
        wipe_json(&mut value);
        let mut encoded = encoded?;
        if encoded.len() > crate::host::MAX_PRIVATE_BYTES {
            encoded.zeroize();
            return Err(LIMIT);
        }
        let token = match self.token() {
            Ok(token) => token,
            Err(error) => {
                encoded.zeroize();
                return Err(error);
            }
        };
        self.private_results.insert(token, encoded);
        Ok(token)
    }
}
/// # Safety
/// bytes/length and out_result must satisfy the C header's memory contract.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_session_stage_private(
    session: u64,
    bytes: *const u8,
    length: usize,
    out_result: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_result)? };
        let stage: crate::host::Stage = serde_json::from_slice(unsafe { input(bytes, length)? })
            .map_err(|_| INVALID_ARGUMENT)?;
        let mut registry = registry();
        if registry.results.len() >= MAX_RESULTS {
            return Err(LIMIT);
        }
        let state = registry.sessions.get_mut(&session).ok_or(INVALID_HANDLE)?;
        state
            .host
            .as_mut()
            .ok_or(INVALID_STATE)?
            .stage(stage)
            .map_err(host_error)?;
        let result = registry.result(status("staged"))?;
        unsafe { out_result.write(result) };
        Ok(())
    })
}
/// # Safety
/// bytes/length and out_result must satisfy the C header's memory contract.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_session_notify(
    session: u64,
    bytes: *const u8,
    length: usize,
    out_result: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_result)? };
        let notice: crate::host::Notice = serde_json::from_slice(unsafe { input(bytes, length)? })
            .map_err(|_| INVALID_ARGUMENT)?;
        let mut registry = registry();
        if registry.results.len() >= MAX_RESULTS {
            return Err(LIMIT);
        }
        let state = registry.sessions.get_mut(&session).ok_or(INVALID_HANDLE)?;
        if !matches!(state.phase, Phase::Complete(_)) {
            return Err(INVALID_STATE);
        }
        let host = state.host.as_mut().ok_or(INVALID_STATE)?;
        if host.notify(notice).map_err(host_error)? && host.cas_metadata().is_none() {
            state.next_request = state.next_request.checked_add(1).ok_or(LIMIT)?;
            host.begin_cas(state.next_request).map_err(host_error)?;
        }
        let value = match host.cas_metadata() {
            Some(request) => json!({"abiVersion":1,"status":"need_host","request":request}),
            None => host.public_status(),
        };
        let result = registry.result(value)?;
        unsafe { out_result.write(result) };
        Ok(())
    })
}
/// Return a separately owned PRIVATE buffer token, never a normal result token.
/// # Safety
/// out_private must address writable storage for one uint64_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_session_private_data(
    session: u64,
    kind: u32,
    out_private: *mut u64,
) -> i32 {
    guard(|| {
        unsafe { output(out_private)? };
        let mut registry = registry();
        if registry.private_results.len() >= MAX_PRIVATE_RESULTS {
            return Err(LIMIT);
        }
        let host = registry
            .sessions
            .get(&session)
            .ok_or(INVALID_HANDLE)?
            .host
            .as_ref()
            .ok_or(INVALID_STATE)?;
        let value = match kind {
            PRIVATE_REQUEST => host.private_arguments(),
            PRIVATE_JOURNAL => host.private_journal(),
            _ => return Err(INVALID_ARGUMENT),
        }
        .map_err(host_error)?;
        let token = registry.private_result(value)?;
        unsafe { out_private.write(token) };
        Ok(())
    })
}
/// # Safety
/// out_length must address writable storage for one size_t.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_private_length(token: u64, out_length: *mut usize) -> i32 {
    guard(|| {
        if out_length.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        unsafe { out_length.write(0) };
        let registry = registry();
        let value = registry.private_results.get(&token).ok_or(INVALID_HANDLE)?;
        unsafe { out_length.write(value.len()) };
        Ok(())
    })
}
/// # Safety
/// destination and out_written follow the C header's writable-memory contract.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn nightlean_private_copy(
    token: u64,
    destination: *mut u8,
    capacity: usize,
    out_written: *mut usize,
) -> i32 {
    guard(|| {
        if out_written.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        unsafe { out_written.write(0) };
        let registry = registry();
        let value = registry.private_results.get(&token).ok_or(INVALID_HANDLE)?;
        if capacity < value.len() {
            return Err(BUFFER_TOO_SMALL);
        }
        if destination.is_null() {
            return Err(INVALID_ARGUMENT);
        }
        unsafe {
            ptr::copy_nonoverlapping(value.as_ptr(), destination, value.len());
            out_written.write(value.len())
        };
        Ok(())
    })
}
#[unsafe(no_mangle)]
pub extern "C" fn nightlean_private_free(token: u64) -> i32 {
    guard(|| {
        let mut value = registry()
            .private_results
            .remove(&token)
            .ok_or(INVALID_HANDLE)?;
        value.zeroize();
        Ok(())
    })
}
