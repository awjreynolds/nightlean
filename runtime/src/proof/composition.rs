use super::{
    Abort, ContractAction, Error, Material, NativeIntent, ProofPreimageVersioned, ProofRequest,
    ProofService, ProofVersioned, ProvedIntent, Result, SelectedProof, ServiceError,
    TrustedParameters, VerifiedBundle, preview_call_activity, prove_intent,
};
use crate::Db;
use futures::Future;
use ledger::structure::LedgerState;
use rand::{CryptoRng, Rng, SeedableRng, rngs::StdRng};
use std::{cell::RefCell, collections::BTreeSet};
use transient_crypto::{
    curve::Fr,
    proofs::{KeyLocation, Zkir},
};

/// Authenticated artifacts and trusted SRS for one call in intent order.
pub struct CompositionMaterial<'a> {
    pub bundle: &'a VerifiedBundle,
    pub parameters: &'a TrustedParameters,
}

struct FrozenCall<'a> {
    key: KeyLocation,
    material: Material,
    parameters: &'a TrustedParameters,
    statement: Vec<Fr>,
    activity: Vec<Option<usize>>,
}

/// A frozen native intent with each operation bound to a verifier in a trusted ledger snapshot.
pub struct PreparedComposition<'a> {
    intent: NativeIntent,
    calls: Vec<FrozenCall<'a>>,
}

impl<'a> PreparedComposition<'a> {
    /// Use a host-authenticated snapshot for key and ledger parameter agreement.
    /// Pass one material selection per call, in the same order as the intent.
    pub fn from_intent(
        intent: NativeIntent,
        snapshot: &LedgerState<Db>,
        material: &[CompositionMaterial<'a>],
    ) -> Result<Self> {
        if intent.actions.is_empty()
            || intent.actions.len() != material.len()
            || intent.dust_actions.is_some()
            || intent.guaranteed_unshielded_offer.is_some()
            || intent.fallible_unshielded_offer.is_some()
        {
            return Err(Error::InvalidIntent);
        }
        let mut calls = Vec::with_capacity(material.len());
        let mut commitments = BTreeSet::new();
        for (action, selection) in intent.actions.iter_deref().zip(material) {
            let ContractAction::Call(call) = action else {
                return Err(Error::InvalidIntent);
            };
            let ProofPreimageVersioned::V2(preimage) = &call.proof else {
                return Err(Error::InvalidIntent);
            };
            let material = Material::retained(selection.bundle)?;
            let parameters = selection.parameters;
            let mut retained_parameters = material.parameters.clone();
            // Fee prices change per block. Funding uses the live snapshot's prices.
            retained_parameters.fee_prices = snapshot.parameters.fee_prices.clone();
            if parameters.k() != material.circuit.k() || retained_parameters != *snapshot.parameters
            {
                return Err(Error::InvalidParameters);
            }
            let deployed = snapshot
                .contract
                .get(&call.address)
                .ok_or(Error::BindingMismatch)?;
            let installed = deployed
                .operations
                .get(&call.entry_point)
                .ok_or(Error::BindingMismatch)?;
            if installed.latest() != Some(&material.verifier)
                || call.entry_point.0 != material.entrypoint.as_bytes()
                || preimage.key_location.0.as_ref()
                    != format!("{}:{}", hex::encode(call.address.0.0), material.entrypoint)
                || !commitments.insert(call.communication_commitment)
            {
                return Err(Error::BindingMismatch);
            }
            let (commitment, opening) = preimage
                .communications_commitment
                .ok_or(Error::BindingMismatch)?;
            if commitment != call.communication_commitment || opening == Fr::from(0u64) {
                return Err(Error::BindingMismatch);
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
            let mut bound = (**preimage).clone();
            bound.binding_input = preview.statement[0];
            if bound
                .check(&material.circuit)
                .map_err(|_| Error::BindingMismatch)?
                != activity
            {
                return Err(Error::BindingMismatch);
            }
            calls.push(FrozenCall {
                key: preimage.key_location.clone(),
                material,
                parameters,
                statement: preview.statement,
                activity,
            });
        }
        Ok(Self { intent, calls })
    }

    /// Attach and independently verify one proof per call. All calls share the same intent binding.
    pub async fn prove<S: ProofService>(
        &self,
        service: &S,
        max_response_bytes: usize,
        stop: impl Future<Output = Abort>,
    ) -> Result<ProvedIntent> {
        let calls: Vec<_> = self
            .calls
            .iter()
            .map(|call| SelectedProof {
                key: &call.key,
                material: &call.material,
                statement: &call.statement,
                activity: &call.activity,
                parameters: call.parameters,
            })
            .collect();
        let proved = prove_intent(&self.intent, &calls, service, max_response_bytes, stop).await?;
        if proved.actions.len() != calls.len() {
            return Err(Error::Attachment);
        }
        for (action, call) in proved.actions.iter_deref().zip(calls) {
            let ContractAction::Call(attached) = action else {
                return Err(Error::Attachment);
            };
            let ProofVersioned::V3(proof) = &attached.proof else {
                return Err(Error::Attachment);
            };
            if attached
                .public_inputs(proved.binding_commitment.into())
                .map_err(|_| Error::Attachment)?
                != call.statement
            {
                return Err(Error::BindingMismatch);
            }
            call.material
                .verifier
                .verify(
                    &call.parameters.verifier,
                    proof,
                    call.statement.iter().copied(),
                )
                .map_err(|_| Error::InvalidProof)?;
        }
        ProvedIntent::checked_encoding(proved, None)
    }

    /// Prove every call on the host, with fresh entropy for each request.
    pub async fn prove_locally(
        &self,
        rng: impl Rng + CryptoRng,
        stop: impl Future<Output = Abort>,
    ) -> Result<ProvedIntent> {
        struct Local<R>(RefCell<R>);
        impl<R: Rng + CryptoRng> ProofService for Local<R> {
            async fn prove(
                &self,
                request: ProofRequest<'_>,
            ) -> std::result::Result<Vec<u8>, ServiceError> {
                let rng = StdRng::from_rng(&mut *self.0.borrow_mut()).map_err(|_| ServiceError)?;
                request.prove_locally(rng).await
            }
        }
        self.prove(&Local(RefCell::new(rng)), super::MAX_RESPONSE, stop)
            .await
    }
}
