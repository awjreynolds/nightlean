use js_sys::Uint8Array;
use noctium_runtime::{
    browser_transport::{decode_reply, transaction_request},
    control_ffi as ffi,
    witness_execution::{WitnessClient, WitnessClientCommand},
};
use serde::Serialize;
use wasm_bindgen::prelude::*;
use zeroize::Zeroizing;

use crate::{MAX_BYTES, input};

pub(crate) const MAX_DESCRIPTOR: usize = 65_536;
const MAX_RECOVERY_CONTEXT: usize = 1_200_000;
const MAX_PRIVATE_REQUEST: usize = 32 * MAX_BYTES;
const MAX_WIRE_MESSAGE: usize = 70 * MAX_BYTES;

fn bytes(value: &[u8], limit: usize) -> Result<Uint8Array, JsValue> {
    if value.len() > limit {
        return Err(JsValue::from(ffi::LIMIT));
    }
    Ok(Uint8Array::from(value))
}

fn json(value: &impl Serialize, limit: usize) -> Result<Uint8Array, JsValue> {
    let encoded =
        Zeroizing::new(serde_json::to_vec(value).map_err(|_| JsValue::from(ffi::INTERNAL))?);
    bytes(&encoded, limit)
}

/// Drives one native ledger attempt through the application's host services.
#[wasm_bindgen]
pub struct BrowserClient(pub(crate) WitnessClient);

#[wasm_bindgen]
impl BrowserClient {
    /// Reload an attempt through the trusted journal service.
    pub fn recover(
        descriptor: &Uint8Array,
        context: &Uint8Array,
    ) -> Result<BrowserClient, JsValue> {
        let descriptor = input(descriptor, MAX_DESCRIPTOR)?;
        let context = input(context, MAX_RECOVERY_CONTEXT)?;
        let mut client = WitnessClient::recover(&descriptor, &context)
            .map_err(|_| JsValue::from(ffi::INVALID_ARGUMENT))?;
        client
            .poll()
            .map_err(|_| JsValue::from(ffi::INVALID_STATE))?;
        Ok(Self(client))
    }

    pub fn status(&self) -> Result<Uint8Array, JsValue> {
        json(&self.0.status(), MAX_BYTES)
    }

    pub fn command(&mut self, command: &str) -> Result<Uint8Array, JsValue> {
        let command = match command {
            "prepare" => WitnessClientCommand::Prepare,
            "submit" => WitnessClientCommand::Submit,
            "observe" => WitnessClientCommand::Observe,
            "commit" => WitnessClientCommand::Commit,
            "cancel" => WitnessClientCommand::Cancel,
            "deadline" => WitnessClientCommand::Deadline,
            "reload" => WitnessClientCommand::Reload,
            _ => return Err(JsValue::from(ffi::INVALID_ARGUMENT)),
        };
        let value = self
            .0
            .command(command)
            .map_err(|_| JsValue::from(ffi::INVALID_STATE))?;
        json(&value, MAX_BYTES)
    }

    pub fn poll(&mut self) -> Result<Uint8Array, JsValue> {
        let value = self
            .0
            .poll()
            .map_err(|_| JsValue::from(ffi::INVALID_STATE))?;
        json(&value, MAX_BYTES)
    }

    /// Metadata for the pending host request, or empty bytes.
    pub fn request(&self) -> Result<Uint8Array, JsValue> {
        let request = self
            .0
            .request_metadata()
            .map_err(|_| JsValue::from(ffi::INVALID_STATE))?;
        match request {
            Some(metadata) => json(&metadata, MAX_BYTES),
            None => bytes(&[], MAX_BYTES),
        }
    }

    /// Private service arguments. Send only to the configured trusted service.
    #[wasm_bindgen(js_name = privateRequest)]
    pub fn private_request(&self) -> Result<Uint8Array, JsValue> {
        let request = self
            .0
            .request()
            .map_err(|_| JsValue::from(ffi::INVALID_STATE))?;
        bytes(
            request
                .as_ref()
                .and_then(|value| value.private_payload())
                .unwrap_or_default(),
            MAX_PRIVATE_REQUEST,
        )
    }

    /// Exact public transaction binding for pending submit and observe requests, or empty bytes.
    #[wasm_bindgen(js_name = transactionRequest)]
    pub fn transaction_request(&self) -> Result<Uint8Array, JsValue> {
        let request = self
            .0
            .request()
            .map_err(|_| JsValue::from(ffi::INVALID_STATE))?;
        match request.as_ref().and_then(|value| value.transaction()) {
            Some(transaction) => json(&transaction_request(transaction), MAX_WIRE_MESSAGE),
            None => bytes(&[], MAX_WIRE_MESSAGE),
        }
    }

    pub fn complete(
        &mut self,
        request_id: &str,
        reply: &Uint8Array,
    ) -> Result<Uint8Array, JsValue> {
        let id = request_id
            .parse::<u64>()
            .ok()
            .filter(|id| *id > 0 && id.to_string() == request_id)
            .ok_or_else(|| JsValue::from(ffi::INVALID_RESPONSE))?;
        if self.0.status()["requestId"].as_str() != Some(request_id) {
            return Err(JsValue::from(ffi::INVALID_RESPONSE));
        }
        let wire = input(reply, MAX_WIRE_MESSAGE)?;
        let reply = decode_reply(&wire).map_err(|_| JsValue::from(ffi::INVALID_RESPONSE))?;
        let status = self
            .0
            .complete(id, reply)
            .map_err(|_| JsValue::from(ffi::INVALID_RESPONSE))?;
        json(&status, MAX_BYTES)
    }

    /// Private host context for reloading the attempt after a worker restart.
    #[wasm_bindgen(js_name = recoveryContext)]
    pub fn recovery_context(&self) -> Result<Uint8Array, JsValue> {
        let context = self
            .0
            .recovery_context()
            .map_err(|_| JsValue::from(ffi::INVALID_STATE))?;
        bytes(context, MAX_RECOVERY_CONTEXT)
    }

    /// The exact contract state from the verified finalized receipt.
    #[wasm_bindgen(js_name = receiptState)]
    pub fn receipt_state(&self) -> Result<Uint8Array, JsValue> {
        let state = self
            .0
            .receipt_state()
            .map_err(|_| JsValue::from(ffi::INVALID_STATE))?;
        bytes(&state, MAX_BYTES)
    }

    pub fn detachable(&self) -> bool {
        self.0.detachable()
    }
}
