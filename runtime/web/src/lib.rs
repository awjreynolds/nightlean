//! Browser adapter for the same bounded Control ABI used by native hosts.
use js_sys::Uint8Array;
use noctium_runtime::{control::MAX_BYTES, control_ffi as ffi};
use wasm_bindgen::prelude::*;
use zeroize::Zeroizing;

fn status(code: i32) -> Result<(), JsValue> {
    if code == ffi::OK {
        Ok(())
    } else {
        Err(JsValue::from(code))
    }
}

fn input(bytes: &Uint8Array) -> Result<Zeroizing<Vec<u8>>, JsValue> {
    let len = bytes.length() as usize;
    if len == 0 {
        return Err(JsValue::from(ffi::INVALID_ARGUMENT));
    }
    if len > MAX_BYTES {
        return Err(JsValue::from(ffi::LIMIT));
    }
    let mut copy = Zeroizing::new(vec![0; len]);
    bytes.copy_to(&mut copy);
    Ok(copy)
}

struct ResultAccess {
    length: unsafe extern "C" fn(u64, *mut usize) -> i32,
    copy: unsafe extern "C" fn(u64, *mut u8, usize, *mut usize) -> i32,
    free: extern "C" fn(u64) -> i32,
}

const RESULT: ResultAccess = ResultAccess {
    length: ffi::noctium_control_result_length,
    copy: ffi::noctium_control_result_copy,
    free: ffi::noctium_control_result_free,
};
const PRIVATE: ResultAccess = ResultAccess {
    length: ffi::noctium_control_private_length,
    copy: ffi::noctium_control_private_copy,
    free: ffi::noctium_control_private_free,
};

impl ResultAccess {
    fn take(&self, token: u64) -> Result<Uint8Array, JsValue> {
        let result = (|| {
            let mut size = 0;
            status(unsafe { (self.length)(token, &mut size) })?;
            if size == 0 || size > MAX_BYTES {
                return Err(JsValue::from(ffi::INTERNAL));
            }
            let mut bytes = Zeroizing::new(vec![0u8; size]);
            let mut written = 0;
            status(unsafe { (self.copy)(token, bytes.as_mut_ptr(), size, &mut written) })?;
            if written != size {
                return Err(JsValue::from(ffi::INTERNAL));
            }
            Ok(Uint8Array::from(bytes.as_slice()))
        })();
        let released = (self.free)(token);
        result.and_then(|bytes| {
            status(released)?;
            Ok(bytes)
        })
    }
}

/// Runs a Noctium host-control witness. Byte arrays contain UTF-8 JSON.
/// Status failures throw the numeric Control ABI code.
#[wasm_bindgen]
pub struct WitnessSession {
    handle: Option<u64>,
}

#[wasm_bindgen]
impl WitnessSession {
    #[wasm_bindgen(constructor)]
    pub fn open(begin: &Uint8Array) -> Result<WitnessSession, JsValue> {
        let bytes = input(begin)?;
        let mut handle = 0;
        status(unsafe { ffi::noctium_control_begin(bytes.as_ptr(), bytes.len(), &mut handle) })?;
        Ok(Self {
            handle: Some(handle),
        })
    }

    pub fn advance(&self) -> Result<Uint8Array, JsValue> {
        self.result(&RESULT, |handle, result| unsafe {
            ffi::noctium_control_advance(handle, result)
        })
    }

    /// Resume an exact correlated request. Pass false for a v1 reply.
    pub fn resume(&self, response: &Uint8Array, typed: bool) -> Result<Uint8Array, JsValue> {
        let bytes = input(response)?;
        let resume = if typed {
            ffi::noctium_control_resume_typed
        } else {
            ffi::noctium_control_resume
        };
        self.result(&RESULT, |handle, result| unsafe {
            resume(handle, bytes.as_ptr(), bytes.len(), result)
        })
    }

    /// Private provider arguments and staged writes. Keep these bytes on the trusted host.
    #[wasm_bindgen(js_name = privateRequest)]
    pub fn private_request(&self) -> Result<Uint8Array, JsValue> {
        self.result(&PRIVATE, |handle, result| unsafe {
            ffi::noctium_control_private_request(handle, result)
        })
    }

    pub fn cancel(&self) -> Result<Uint8Array, JsValue> {
        self.result(&RESULT, |handle, result| unsafe {
            ffi::noctium_control_cancel(handle, result)
        })
    }

    pub fn close(&mut self) -> Result<(), JsValue> {
        if let Some(handle) = self.handle {
            status(ffi::noctium_control_free(handle))?;
            self.handle = None;
        }
        Ok(())
    }
}

impl WitnessSession {
    fn result(
        &self,
        access: &ResultAccess,
        action: impl FnOnce(u64, &mut u64) -> i32,
    ) -> Result<Uint8Array, JsValue> {
        let handle = self
            .handle
            .ok_or_else(|| JsValue::from(ffi::INVALID_HANDLE))?;
        let mut token = 0;
        status(action(handle, &mut token))?;
        access.take(token)
    }
}

impl Drop for WitnessSession {
    fn drop(&mut self) {
        let _ = self.close();
    }
}
