use super::{
    Abort, ContractAction, ContractCall, Error, Material, NativeIntent, ProofKind, ProofMarker,
    ProofPreimageVersioned, ProofRequest, ProofService, ProofVersioned, ProvedIntent,
    ProvedNativeIntent, Result, SelectedProof, ServiceError, TrustedParameters, VerifiedBundle,
    preview_call_activity, prove_intent, verify_service_response,
};
use crate::{
    Db,
    assembly::{CheckedNativeCall, CompositionOffer, partition_composition},
    composition_wire::{self, MAX_DRAFT_BYTES, MAX_DRAFT_CALLS, PublicContext, PublicDraft},
};
use base_crypto::time::Timestamp;
use futures::Future;
use ledger::structure::{Intent, LedgerState, Signature, StandardTransaction};
use rand::{CryptoRng, Rng, SeedableRng, rngs::StdRng};
use sha2::{Digest, Sha256};
use std::{cell::RefCell, collections::BTreeSet};
use storage::arena::Sp;
use transient_crypto::{
    commitment::{Pedersen, PedersenRandomness},
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
            let material = material_for_call(call, snapshot, selection)?;
            let parameters = selection.parameters;
            if preimage.key_location.0.as_ref()
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

fn material_for_call<P: ProofKind<Db>>(
    call: &ContractCall<P, Db>,
    snapshot: &LedgerState<Db>,
    selection: &CompositionMaterial<'_>,
) -> Result<Material> {
    let material = Material::retained(selection.bundle)?;
    let mut retained_parameters = material.parameters.clone();
    // Fee prices change per block. Funding uses the live snapshot's prices.
    retained_parameters.fee_prices = snapshot.parameters.fee_prices.clone();
    if selection.parameters.k() != material.circuit.k()
        || retained_parameters != *snapshot.parameters
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
    {
        return Err(Error::BindingMismatch);
    }
    Ok(material)
}

/// Public request shared with the witness owners. Every owner should approve the ordered
/// calls, commitment and expiry before proving. The draft holds neither kind of opening.
#[derive(Clone)]
pub struct CompositionDraft {
    offers: Vec<CompositionOffer>,
    calls: Vec<ContractCall<(), Db>>,
    binding: Pedersen,
    ttl: u64,
    network_id: String,
}

impl CompositionDraft {
    /// Recompute the public draft from the agreed offers and binding commitment.
    pub fn from_offers(
        offers: &[CompositionOffer],
        snapshot: &LedgerState<Db>,
        binding: Pedersen,
        ttl: u64,
    ) -> Result<Self> {
        if ttl == 0 {
            return Err(Error::InvalidIntent);
        }
        let partitioned = partition_composition(offers, &snapshot.parameters)
            .map_err(|_| Error::InvalidIntent)?;
        let cost = &snapshot.parameters.cost_model.runtime_cost_model;
        let calls = partitioned
            .iter()
            .zip(offers)
            .map(|(call, offer)| {
                preview_call_activity(call, &offer.activity, binding, cost)
                    .map(|preview| preview.call)
            })
            .collect::<Result<Vec<_>>>()?;
        let public: Intent<Signature, (), Pedersen, Db> = Intent {
            guaranteed_unshielded_offer: None,
            fallible_unshielded_offer: None,
            actions: calls
                .iter()
                .cloned()
                .map(|call| ContractAction::Call(Sp::new(call)))
                .collect(),
            dust_actions: None,
            ttl: Timestamp::from_secs(ttl),
            binding_commitment: binding,
        };
        StandardTransaction {
            network_id: snapshot.network_id.clone(),
            binding_randomness: Default::default(),
            intents: [(1, public)].into_iter().collect(),
            guaranteed_coins: None,
            fallible_coins: Default::default(),
        }
        .sequencing_check()
        .map_err(|_| Error::InvalidIntent)?;
        Ok(Self {
            offers: offers.to_vec(),
            calls,
            binding,
            ttl,
            network_id: snapshot.network_id.clone(),
        })
    }

    fn calls_sha256(&self) -> Result<[u8; 32]> {
        let bytes =
            composition_wire::encode(&self.calls, MAX_DRAFT_BYTES).map_err(|_| Error::Limit)?;
        Ok(Sha256::digest(bytes).into())
    }

    /// Encode the full ordered public draft, including a digest of its partitioned calls.
    pub fn public_bytes(&self) -> Result<Vec<u8>> {
        if self.offers.len() > MAX_DRAFT_CALLS {
            return Err(Error::Limit);
        }
        let mut budget = MAX_DRAFT_BYTES;
        let mut offers = Vec::with_capacity(self.offers.len());
        for offer in &self.offers {
            let bytes = offer.public_bytes().map_err(|_| Error::Limit)?;
            budget = budget.checked_sub(bytes.len()).ok_or(Error::Limit)?;
            offers.push(bytes);
        }
        composition_wire::encode(
            &PublicDraft {
                profile: crate::profile::NAME.into(),
                network_id: self.network_id.clone(),
                ttl: self.ttl,
                binding: self.binding,
                offers,
                calls_sha256: self.calls_sha256()?,
            },
            MAX_DRAFT_BYTES,
        )
        .map_err(|_| Error::Limit)
    }

    /// Import a public draft from the host's authenticated channel and rebuild its
    /// exact partitioned calls against the host's trusted snapshot.
    pub fn from_public_bytes(bytes: &[u8], snapshot: &LedgerState<Db>) -> Result<Self> {
        let wire: PublicDraft =
            composition_wire::decode(bytes, MAX_DRAFT_BYTES).map_err(|_| Error::InvalidIntent)?;
        if wire.profile != crate::profile::NAME || wire.network_id != snapshot.network_id {
            return Err(Error::BindingMismatch);
        }
        if wire.offers.len() > MAX_DRAFT_CALLS {
            return Err(Error::Limit);
        }
        let offers = wire
            .offers
            .iter()
            .map(|bytes| {
                CompositionOffer::from_public_bytes(bytes).map_err(|_| Error::InvalidIntent)
            })
            .collect::<Result<Vec<_>>>()?;
        let draft = Self::from_offers(&offers, snapshot, wire.binding, wire.ttl)?;
        if draft.calls_sha256()? != wire.calls_sha256 {
            return Err(Error::BindingMismatch);
        }
        Ok(draft)
    }

    pub fn calls(&self) -> &[ContractCall<(), Db>] {
        &self.calls
    }

    pub fn binding_commitment(&self) -> Pedersen {
        self.binding
    }

    pub fn ttl(&self) -> u64 {
        self.ttl
    }

    /// Produce only the requested slot's proof, using this owner's private execution locally.
    pub async fn prove_call(
        &self,
        index: usize,
        own_call: &CheckedNativeCall<'_>,
        snapshot: &LedgerState<Db>,
        selection: &CompositionMaterial<'_>,
        rng: impl Rng + CryptoRng,
    ) -> Result<Vec<u8>> {
        let expected = self.offers.get(index).ok_or(Error::InvalidIntent)?;
        let call = &self.calls[index];
        let own = own_call
            .composition_offer(&snapshot.parameters)
            .map_err(|_| Error::InvalidIntent)?;
        let before = &expected.pre_transcript;
        let actual = &own.pre_transcript;
        if own.entry_point != expected.entry_point
            || own.activity != expected.activity
            || own.commitment() != expected.commitment()
            || actual.program != before.program
            || actual.context.address != before.context.address
            || actual.context.state != before.context.state
            || PublicContext::from(&actual.context.call_context)
                != PublicContext::from(&before.context.call_context)
        {
            return Err(Error::BindingMismatch);
        }
        let material = material_for_call(call, snapshot, selection)?;
        let statement = call
            .public_inputs(self.binding)
            .map_err(|_| Error::InvalidIntent)?;
        let mut preimage = own_call.composition_preimage(&own);
        preimage.binding_input = statement[0];
        if preimage
            .check(&material.circuit)
            .map_err(|_| Error::InvalidIntent)?
            != own.activity
        {
            return Err(Error::BindingMismatch);
        }
        let response = ProofRequest {
            preimage: &preimage,
            material: &material.native,
            prover: &material.prover,
            parameters: selection.parameters,
            max_response_bytes: super::MAX_RESPONSE,
            expected_statement: &statement,
            expected_activity: &own.activity,
        }
        .prove_locally(rng)
        .await
        .map_err(|_| Error::Service)?;
        verify_service_response(
            &material.verifier,
            selection.parameters,
            &statement,
            &response,
            super::MAX_RESPONSE,
        )?;
        Ok(response)
    }
}

/// Coordinator-owned commitment randomness and its exact public draft. This API receives
/// public offers and proofs. Only the individual owners provide private executions.
pub struct IndependentComposition {
    opening: PedersenRandomness,
    draft: CompositionDraft,
}

impl IndependentComposition {
    pub fn freeze(
        offers: &[CompositionOffer],
        snapshot: &LedgerState<Db>,
        ttl: u64,
        rng: &mut (impl Rng + CryptoRng),
    ) -> Result<Self> {
        let opening = NativeIntent::empty(rng, Timestamp::from_secs(ttl)).binding_randomness();
        let draft = CompositionDraft::from_offers(offers, snapshot, opening.into(), ttl)?;
        Ok(Self { opening, draft })
    }

    pub fn draft(&self) -> &CompositionDraft {
        &self.draft
    }

    /// Verify each detached proof against its frozen slot and attach to the same intent.
    pub fn attach(
        &self,
        responses: &[Vec<u8>],
        snapshot: &LedgerState<Db>,
        selected: &[CompositionMaterial<'_>],
    ) -> Result<ProvedIntent> {
        if responses.len() != self.draft.calls.len() || responses.len() != selected.len() {
            return Err(Error::InvalidResponse);
        }
        let mut actions = Vec::with_capacity(responses.len());
        for ((call, response), selection) in self.draft.calls.iter().zip(responses).zip(selected) {
            let material = material_for_call(call, snapshot, selection)?;
            let statement = call
                .public_inputs(self.draft.binding)
                .map_err(|_| Error::InvalidIntent)?;
            let proof = verify_service_response(
                &material.verifier,
                selection.parameters,
                &statement,
                response,
                super::MAX_RESPONSE,
            )?;
            actions.push(ContractAction::<ProofMarker, Db>::Call(Sp::new(
                ContractCall {
                    address: call.address,
                    entry_point: call.entry_point.clone(),
                    guaranteed_transcript: call.guaranteed_transcript.clone(),
                    fallible_transcript: call.fallible_transcript.clone(),
                    communication_commitment: call.communication_commitment,
                    proof: ProofVersioned::V3(proof),
                },
            )));
        }
        let intent = ProvedNativeIntent {
            guaranteed_unshielded_offer: None,
            fallible_unshielded_offer: None,
            actions: actions.into(),
            dust_actions: None,
            ttl: Timestamp::from_secs(self.draft.ttl),
            binding_commitment: self.opening,
        };
        ProvedIntent::checked_encoding(intent, None)
    }
}
