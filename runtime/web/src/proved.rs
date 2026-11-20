use std::{collections::BTreeMap, future::pending};

use js_sys::{Array, Uint8Array};
use noctium_runtime::{
    artifacts::{self, VerifiedBundle},
    control_ffi as ffi, host, profile,
    proof::{self, LocalProver, TrustedParameters},
    witness_execution::{Error, WitnessExecution, WitnessProof, WitnessProvedCall},
};
use rand::{
    RngCore, SeedableRng,
    rngs::{OsRng, StdRng},
};
use serde::Deserialize;
use serde_json::Value;
use wasm_bindgen::{JsCast, prelude::*};
use zeroize::Zeroizing;

use crate::{
    MAX_BYTES,
    client::{BrowserClient, MAX_DESCRIPTOR},
    input,
};

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Target {
    abi_version: u32,
    profile: String,
    trusted_manifest_sha256: String,
    proof_parameters_sha256: String,
    k: u8,
    ttl: u64,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase", deny_unknown_fields)]
struct Begin {
    abi_version: u32,
    host_context: host::Context,
    inputs: BTreeMap<String, Value>,
}

fn fresh_rng() -> Result<StdRng, JsValue> {
    let mut seed = Zeroizing::new([0; 32]);
    OsRng
        .try_fill_bytes(seed.as_mut())
        .map_err(|_| JsValue::from(ffi::INTERNAL))?;
    Ok(StdRng::from_seed(*seed))
}

fn execution_failure(error: Error) -> JsValue {
    JsValue::from(match error {
        Error::State | Error::InvalidSource => ffi::INVALID_STATE,
        Error::ResourceLimit | Error::Proof(proof::Error::Limit) => ffi::LIMIT,
        Error::Proof(proof::Error::InvalidProof | proof::Error::InvalidResponse) => {
            ffi::INVALID_RESPONSE
        }
        _ => ffi::INVALID_ARGUMENT,
    })
}

fn encode(value: &Value) -> Result<Uint8Array, JsValue> {
    let bytes =
        Zeroizing::new(serde_json::to_vec(value).map_err(|_| JsValue::from(ffi::INTERNAL))?);
    if bytes.len() > MAX_BYTES {
        return Err(JsValue::from(ffi::LIMIT));
    }
    Ok(Uint8Array::from(bytes.as_slice()))
}

struct Invocation {
    bundle: VerifiedBundle,
    execution: WitnessExecution,
    parameters: TrustedParameters,
    ttl: u64,
}

/// Runs the exact witness in a pinned bundle with its matching proof parameters.
#[wasm_bindgen]
pub struct AuthenticatedWitness(Option<Invocation>);

#[wasm_bindgen]
impl AuthenticatedWitness {
    /// Supply payloads in the canonical manifest entry order.
    #[wasm_bindgen(constructor)]
    pub fn new(
        descriptor: &Uint8Array,
        manifest: &Uint8Array,
        payloads: &Array,
        srs: &Uint8Array,
        state: &Uint8Array,
        begin: &Uint8Array,
    ) -> Result<AuthenticatedWitness, JsValue> {
        let invalid = |_| JsValue::from(ffi::INVALID_ARGUMENT);
        let target: Target =
            serde_json::from_slice(&input(descriptor, 65_536)?).map_err(invalid)?;
        if target.abi_version != 1 || target.profile != profile::NAME || target.ttl == 0 {
            return Err(JsValue::from(ffi::INVALID_ARGUMENT));
        }
        let bundle = artifacts::verify_memory_with_limit(
            &input(manifest, artifacts::MAX_JSON_BYTES as usize)?,
            &target.trusted_manifest_sha256,
            16 * 1024 * 1024,
            payloads.length() as usize,
            |index, size| {
                let bytes = payloads.get(index as u32).dyn_into::<Uint8Array>().ok()?;
                (bytes.length() as usize == size).then(|| bytes.to_vec())
            },
        )
        .map_err(|error| {
            JsValue::from(if error.code == "limit_exceeded" {
                ffi::LIMIT
            } else {
                ffi::INVALID_ARGUMENT
            })
        })?;
        let parameters = TrustedParameters::from_bytes(
            &input(srs, 128 * 1024 * 1024)?,
            target.k,
            &target.proof_parameters_sha256,
        )
        .map_err(|_| JsValue::from(ffi::INVALID_ARGUMENT))?;
        let state = input(state, MAX_BYTES)?;
        let mut rng = fresh_rng()?;
        let begin: Begin = serde_json::from_slice(&input(begin, MAX_BYTES)?).map_err(invalid)?;
        if begin.abi_version != 1 {
            return Err(JsValue::from(ffi::INVALID_ARGUMENT));
        }
        let execution = WitnessExecution::begin(
            &bundle,
            &state,
            begin.inputs,
            begin.host_context,
            &parameters,
            target.ttl,
            &mut rng,
        )
        .map_err(execution_failure)?;
        Ok(Self(Some(Invocation {
            bundle,
            execution,
            parameters,
            ttl: target.ttl,
        })))
    }

    pub fn advance(&mut self) -> Result<Uint8Array, JsValue> {
        let result = self
            .active()?
            .execution
            .advance()
            .map_err(execution_failure)?;
        encode(result.as_json())
    }

    #[wasm_bindgen(js_name = privateRequest)]
    pub fn private_request(&mut self) -> Result<Uint8Array, JsValue> {
        let result = self
            .active()?
            .execution
            .private_request()
            .map_err(execution_failure)?;
        encode(result.as_json())
    }

    pub fn resume(&mut self, response: &Uint8Array) -> Result<Uint8Array, JsValue> {
        let bytes = input(response, MAX_BYTES)?;
        let invalid = |_| JsValue::from(ffi::INVALID_RESPONSE);
        let reply = serde_json::from_slice(&bytes).map_err(invalid)?;
        encode(
            &self
                .active()?
                .execution
                .resume_typed(reply)
                .map_err(|_| JsValue::from(ffi::INVALID_RESPONSE))?,
        )
    }

    pub fn cancel(&mut self) -> Result<Uint8Array, JsValue> {
        encode(
            &self
                .active()?
                .execution
                .cancel()
                .map_err(execution_failure)?,
        )
    }

    #[wasm_bindgen(js_name = prepareProof)]
    pub fn prepare_proof(&mut self) -> Result<BrowserProof, JsValue> {
        let invocation = self.active()?;
        let proof = invocation
            .execution
            .prepare_proof(&invocation.bundle, invocation.ttl, &mut fresh_rng()?)
            .map_err(execution_failure)?;
        let invocation = self
            .0
            .take()
            .ok_or_else(|| JsValue::from(ffi::INVALID_STATE))?;
        Ok(BrowserProof {
            proof,
            parameters: invocation.parameters,
        })
    }
}

impl AuthenticatedWitness {
    fn active(&mut self) -> Result<&mut Invocation, JsValue> {
        self.0
            .as_mut()
            .ok_or_else(|| JsValue::from(ffi::INVALID_STATE))
    }
}

#[wasm_bindgen]
pub struct BrowserProof {
    proof: WitnessProof,
    parameters: TrustedParameters,
}

#[wasm_bindgen]
impl BrowserProof {
    /// Produce and verify the native call proof in the same worker.
    #[wasm_bindgen(js_name = proveLocally)]
    pub async fn prove_locally(&mut self) -> Result<BrowserProvedCall, JsValue> {
        let prover = LocalProver::new(fresh_rng()?);
        self.proof
            .prove(&prover, &self.parameters, MAX_BYTES, pending())
            .await
            .map(BrowserProvedCall)
            .map_err(execution_failure)
    }
}

#[wasm_bindgen]
pub struct BrowserProvedCall(WitnessProvedCall);

#[wasm_bindgen]
impl BrowserProvedCall {
    /// Start the proved call with its original private source Runtime.
    #[wasm_bindgen(js_name = startCallClient)]
    pub fn start_call_client(&mut self, descriptor: &Uint8Array) -> Result<BrowserClient, JsValue> {
        let descriptor = input(descriptor, MAX_DESCRIPTOR)?;
        self.0
            .start_call_client(&descriptor)
            .map(BrowserClient)
            .map_err(execution_failure)
    }

    /// Start deployment for the same proved call with a separate host context.
    #[wasm_bindgen(js_name = startDeploymentClient)]
    pub fn start_deployment_client(
        &mut self,
        descriptor: &Uint8Array,
        setup: &Uint8Array,
    ) -> Result<BrowserClient, JsValue> {
        let descriptor = input(descriptor, MAX_DESCRIPTOR)?;
        let setup = input(setup, MAX_BYTES)?;
        self.0
            .start_deployment_client(&descriptor, &setup)
            .map(BrowserClient)
            .map_err(execution_failure)
    }

    /// Public projection of an unsealed call. The source Runtime and opening stay in WASM.
    #[wasm_bindgen(js_name = publicIntent)]
    pub fn public_intent(&self) -> Result<Uint8Array, JsValue> {
        let bytes = self.0.public_serialized().map_err(execution_failure)?;
        if bytes.len() > MAX_BYTES {
            return Err(JsValue::from(ffi::LIMIT));
        }
        Ok(Uint8Array::from(bytes.as_slice()))
    }
}
