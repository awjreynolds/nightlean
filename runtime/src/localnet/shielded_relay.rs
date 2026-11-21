use super::{DEVELOPMENT_GENESIS, DevelopmentFunding, Error, ProofCache, Result, check};
use super::shielded_transfer::{stage_contract_owned_output, stage_contract_owned_transient};
use crate::{
    Db,
    client::{BoundTransaction, HostFailure, SigningAdapter, Snapshot},
    proof::{
        ContractOperationTarget, CurrentStateCompositionCall, CurrentStateContext,
        TrustedParameters, prepare_relay_destination_composition,
    },
};
use base_crypto::{hash::HashOutput, rng::SplittableRng};
use coin_structure::{
    coin::{Commitment, Info, Nonce, Nullifier},
    contract::ContractAddress,
    transfer::{Recipient, SenderEvidence},
};
use ledger::structure::GUARANTEED_SEGMENT;
use rand::rngs::StdRng;
use serde_json::{Value, json};
use std::{collections::BTreeMap, future::pending};
use transient_crypto::{commitment::PedersenRandomness, curve::Fr, proofs::Proof};
use zswap::{Offer, prove::ZswapResolver};

const RELAY_AMOUNT: u128 = 5;

pub(super) struct BookedRelay {
    pub(super) offer: Offer<Proof, Db>,
    pub(super) randomness: PedersenRandomness,
    pub(super) mint: Info,
    pub(super) domain: HashOutput,
    relay_address: ContractAddress,
    destination_address: ContractAddress,
    relay_state: Vec<u8>,
    destination_state: Vec<u8>,
    transient_commitment: Commitment,
    transient_index: u64,
    transient_nullifier: Nullifier,
    destination_commitment: Commitment,
    destination_index: u64,
}

impl BookedRelay {
    pub(super) fn check_booking(
        &self,
        snapshot: &Snapshot,
    ) -> std::result::Result<(), HostFailure> {
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&self.offer, None)
            .map_err(|_| HostFailure)?;
        let relay = snapshot
            .state
            .contract
            .get(&self.relay_address)
            .ok_or(HostFailure)?;
        let destination = snapshot
            .state
            .contract
            .get(&self.destination_address)
            .ok_or(HostFailure)?;
        let relay_state = tagged_state_bytes(&relay).map_err(|_| HostFailure)?;
        let destination_state = tagged_state_bytes(&destination).map_err(|_| HostFailure)?;
        let Some(transient) = self.offer.transient.get(0) else {
            return Err(HostFailure);
        };
        let Some(output) = self.offer.outputs.get(0) else {
            return Err(HostFailure);
        };

        if relay_state != self.relay_state
            || destination_state != self.destination_state
            || !self.offer.inputs.is_empty()
            || self.offer.outputs.len() != 1
            || self.offer.transient.len() != 1
            || indices.size() != 2
            || self.mint.value != RELAY_AMOUNT
            || transient.coin_com != self.transient_commitment
            || transient.nullifier != self.transient_nullifier
            || transient.contract_address.as_deref() != Some(&self.relay_address)
            || output.coin_com != self.destination_commitment
            || output.contract_address.as_deref() != Some(&self.destination_address)
            || output.ciphertext.is_some()
            || indices.get(&self.transient_commitment).as_deref() != Some(&self.transient_index)
            || indices.get(&self.destination_commitment).as_deref() != Some(&self.destination_index)
            || snapshot
                .state
                .zswap
                .nullifiers
                .contains_key(&self.transient_nullifier)
            || self.transient_commitment
                != self
                    .mint
                    .commitment(&Recipient::Contract(self.relay_address))
            || self.transient_nullifier
                != self
                    .mint
                    .nullifier(&SenderEvidence::Contract(self.relay_address))
            || self.mint.type_ != self.relay_address.custom_shielded_token_type(self.domain)
            || output.coin_com
                != self
                    .mint
                    .evolve_from(
                        b"midnight:kernel:nonce_evolve",
                        self.mint.value,
                        self.mint.type_,
                    )
                    .commitment(&Recipient::Contract(self.destination_address))
        {
            return Err(HostFailure);
        }
        Ok(())
    }
}

impl DevelopmentFunding<'_> {
    /// Book and prove one contract-owned transient forwarded to a second contract call.
    pub async fn bind_shielded_immediate_relay(
        mut self,
        relay_target: &ContractOperationTarget,
        relay_current: &mut Option<CurrentStateContext>,
        relay_inputs: BTreeMap<String, Value>,
        relay_parameters: &TrustedParameters,
        destination_target: &ContractOperationTarget,
        destination_current: &mut Option<CurrentStateContext>,
        destination_parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        mut rng: StdRng,
    ) -> Result<BoundTransaction> {
        let policy = self.node.policy.clone();
        check(policy.genesis == DEVELOPMENT_GENESIS, Error::Policy)?;
        check(
            relay_target.operation() == "forward"
                && destination_target.operation() == "receive"
                && relay_target.contract_address() != destination_target.contract_address(),
            Error::State,
        )?;
        check(relay_inputs.len() == 5, Error::State)?;

        let relay_address = contract_address(relay_target.contract_address())?;
        let destination_address = contract_address(destination_target.contract_address())?;
        let domain = read_bytes32(&relay_inputs, "domain")?;
        let nonce = Nonce(read_bytes32(&relay_inputs, "nonce")?);
        let color = read_bytes32(&relay_inputs, "color")?;
        let recipient = read_bytes32(&relay_inputs, "recipient")?;
        let opening_text = relay_inputs
            .get("opening")
            .and_then(Value::as_str)
            .ok_or(Error::State)?;
        let opening = crate::canonical_field(opening_text).map_err(|_| Error::State)?;
        check(
            crate::field_decimal(opening) == opening_text && opening != Fr::from(0u64),
            Error::State,
        )?;
        let mint_type = relay_address.custom_shielded_token_type(domain);
        check(
            recipient == destination_address.0 && color == mint_type.0,
            Error::State,
        )?;
        let mint = Info {
            nonce,
            type_: mint_type,
            value: RELAY_AMOUNT,
        };
        let destination_coin =
            mint.evolve_from(b"midnight:kernel:nonce_evolve", mint.value, mint.type_);
        let destination_inputs = BTreeMap::from([
            ("nonce".into(), bytes32_json(destination_coin.nonce.0)),
            ("color".into(), bytes32_json(destination_coin.type_.0)),
            ("amount".into(), json!(destination_coin.value.to_string())),
        ]);

        let snapshot = self.node.sync()?;
        snapshot.validate(&policy).map_err(|_| Error::Network)?;
        check(policy == self.node.policy, Error::Policy)?;
        let relay_state = snapshot
            .state
            .contract
            .get(&relay_address)
            .ok_or(Error::State)?;
        let destination_state = snapshot
            .state
            .contract
            .get(&destination_address)
            .ok_or(Error::State)?;
        let relay_state = tagged_state_bytes(&relay_state)?;
        let destination_state = tagged_state_bytes(&destination_state)?;

        let transient = stage_contract_owned_transient(relay_address, &mint, &mut rng)?;
        let destination = stage_contract_owned_output(
            destination_address,
            &destination_coin,
            &mut rng,
        )?;
        let transient_commitment = transient.coin_com;
        let transient_nullifier = transient.nullifier;
        let destination_commitment = destination.commitment;
        let offer =
            Offer::new(vec![], vec![destination.output], vec![transient]).ok_or(Error::State)?;
        let (_, booked_indices) = snapshot
            .state
            .zswap
            .try_apply(&offer, None)
            .map_err(|_| Error::State)?;
        check(booked_indices.size() == 2, Error::State)?;
        let transient_index = *booked_indices
            .get(&transient_commitment)
            .ok_or(Error::State)?;
        let destination_index = *booked_indices
            .get(&destination_commitment)
            .ok_or(Error::State)?;

        let relay_call = CurrentStateCompositionCall {
            target: relay_target,
            current: relay_current,
            parameters: relay_parameters,
            inputs: relay_inputs,
        };
        let destination_call = CurrentStateCompositionCall {
            target: destination_target,
            current: destination_current,
            parameters: destination_parameters,
            inputs: destination_inputs,
        };
        let (prepared, bindings) = prepare_relay_destination_composition(
            relay_call,
            destination_call,
            &snapshot.state,
            &booked_indices,
            opening,
            &mut rng,
        )
        .map_err(|_| Error::Proof)?;
        let proved = prepared
            .prove_locally(rng.split(), pending())
            .await
            .map_err(|_| Error::Proof)?;

        let mut provider = cache.provider.clone();
        provider.expected_data = zswap::ZSWAP_EXPECTED_FILES.to_vec();
        let resolver = ZswapResolver(provider);
        let randomness = offer.binding_randomness();
        let (_, offer) = offer
            .prove(
                builtin_zkir::LocalProvingProvider {
                    rng: rng.split(),
                    resolver: &resolver,
                    params: &resolver,
                },
                GUARANTEED_SEGMENT,
            )
            .await
            .map_err(|_| Error::Proof)?;

        self.shielded_relay = Some(BookedRelay {
            offer,
            randomness,
            mint,
            domain,
            relay_address,
            destination_address,
            relay_state,
            destination_state,
            transient_commitment,
            transient_index,
            transient_nullifier,
            destination_commitment,
            destination_index,
        });
        let expected = &self.shielded_relay.as_ref().ok_or(Error::State)?.offer;
        let bound = BoundTransaction::prepare_shielded_relay(
            proved.native(),
            expected,
            &self.shielded_relay.as_ref().ok_or(Error::State)?.mint,
            domain,
            policy,
            self.node,
            &self,
            signer,
        )
        .await
        .map_err(|_| Error::State)?;
        check(
            bound.expected_state() == bindings[0].expected_state(),
            Error::State,
        )?;
        check(
            bound
                .secondary_states()
                .get(&hex::encode(destination_address.0.0))
                .map(Vec::as_slice)
                == Some(bindings[1].expected_state()),
            Error::State,
        )?;
        Ok(bound)
    }
}

fn contract_address(encoded: &str) -> Result<ContractAddress> {
    let bytes =
        hex::decode(encoded.strip_prefix("0x").unwrap_or(encoded)).map_err(|_| Error::State)?;
    let bytes: [u8; 32] = bytes.try_into().map_err(|_| Error::State)?;
    Ok(ContractAddress(HashOutput(bytes)))
}

fn read_bytes32(inputs: &BTreeMap<String, Value>, name: &str) -> Result<HashOutput> {
    let object = inputs
        .get(name)
        .and_then(Value::as_object)
        .ok_or(Error::State)?;
    check(
        object.len() == 2 && object.get("kind").and_then(Value::as_str) == Some("bytes"),
        Error::State,
    )?;
    let values = object
        .get("values")
        .and_then(Value::as_array)
        .ok_or(Error::State)?;
    check(values.len() == 32, Error::State)?;
    let mut bytes = [0; 32];
    for (output, value) in bytes.iter_mut().zip(values) {
        *output = u8::try_from(value.as_u64().ok_or(Error::State)?).map_err(|_| Error::State)?;
    }
    Ok(HashOutput(bytes))
}

fn bytes32_json(value: HashOutput) -> Value {
    json!({"kind":"bytes", "values":value.0})
}

fn tagged_state_bytes(state: &onchain_runtime::state::ContractState<Db>) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    serialize::tagged_serialize(state, &mut bytes).map_err(|_| Error::State)?;
    Ok(bytes)
}

#[cfg(all(test, feature = "zkir-321"))]
mod tests {
    use super::*;
    use crate::{
        artifacts::{self, ContractBundleSet, Role},
        client::{ChainAdapter, FinalizedReceipt, NetworkPolicy, Submission},
        funding::{CONTRACT_SEGMENT, FeePolicy, UnsealedTransaction},
        localnet::{ExplicitSeal, Node, native_decode},
        proof::WitnessContractTarget,
        zkir::IrSource,
    };
    use anyhow::{Context, Result as TestResult, ensure};
    use base_crypto::fab::AlignedValue;
    use coin_structure::{coin::QualifiedInfo, transfer::Recipient as CoinRecipient};
    use onchain_runtime::state::{ContractState, StateValue};
    use rand::{SeedableRng, rngs::OsRng};
    use std::{
        env,
        path::Path,
        thread,
        time::{Duration, Instant},
    };
    use transient_crypto::proofs::Zkir;

    async fn finalize(node: &Node, bound: &BoundTransaction) -> TestResult<FinalizedReceipt> {
        let sent = node
            .submit(bound)
            .await
            .map_err(|_| anyhow::anyhow!("submit failed"))?;
        ensure!(sent != Submission::Rejected, "node rejected transaction");
        let deadline = Instant::now() + Duration::from_secs(60);
        loop {
            if let Some(receipt) = node.finalized_receipt(bound)? {
                bound.check_receipt(&receipt)?;
                return Ok(receipt);
            }
            ensure!(
                Instant::now() < deadline,
                "finalized receipt did not arrive"
            );
            thread::sleep(Duration::from_millis(500));
        }
    }

    fn bytes32(value: HashOutput) -> Value {
        bytes32_json(value)
    }

    fn inputs(
        domain: HashOutput,
        mint: &Info,
        destination: ContractAddress,
        opening: Fr,
    ) -> BTreeMap<String, Value> {
        BTreeMap::from([
            ("domain".into(), bytes32(domain)),
            ("recipient".into(), bytes32(destination.0)),
            ("nonce".into(), bytes32(mint.nonce.0)),
            ("color".into(), bytes32(mint.type_.0)),
            ("opening".into(), json!(crate::field_decimal(opening))),
        ])
    }

    fn map_coin_by_nonce(state: &ContractState<Db>, nonce: Nonce) -> TestResult<QualifiedInfo> {
        let StateValue::Array(slots) = state.data.get_ref() else {
            anyhow::bail!("expected state array");
        };
        let Some(StateValue::Map(coins)) = slots.get(0) else {
            anyhow::bail!("expected qualified coin Map in slot 0");
        };
        let value = coins
            .get(&AlignedValue::from(nonce))
            .context("qualified coin missing from Destination Map")?;
        let StateValue::Cell(cell) = &*value else {
            anyhow::bail!("qualified coin Map value is not a cell");
        };
        QualifiedInfo::try_from(&*cell.value).map_err(|_| anyhow::anyhow!("invalid qualified coin"))
    }

    fn tree_index(
        snapshot: &Snapshot,
        commitment: Commitment,
        owner: ContractAddress,
    ) -> TestResult<u64> {
        for index in 0..snapshot.state.zswap.first_free {
            if snapshot
                .state
                .zswap
                .coin_coms
                .index(index)
                .is_some_and(|(hash, address)| {
                    hash == commitment.0 && address.as_deref() == Some(&owner)
                })
            {
                return Ok(index);
            }
        }
        anyhow::bail!("booked output commitment missing from finalized tree")
    }

    #[test]
    #[ignore = "requires generated relay/destination bundles and isolated development node"]
    fn funded_shielded_immediate_relay_localnet() -> TestResult<()> {
        futures::executor::block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let relay_bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_RELAY_BUNDLE")?),
                Some(&setting("NOCTIUM_RELAY_MANIFEST_SHA256")?),
            )?;
            let destination_bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_DESTINATION_BUNDLE")?),
                Some(&setting("NOCTIUM_DESTINATION_MANIFEST_SHA256")?),
            )?;
            let relay_circuit = IrSource::load(relay_bundle.file(Role::Circuit)?)?;
            let destination_circuit = IrSource::load(destination_bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_RELAY_PARAMETER_CACHE")?.into(),
                "https://srs.midnight.network/".parse()?,
            )?;
            let policy = NetworkPolicy {
                network_id: "undeployed".into(),
                genesis: DEVELOPMENT_GENESIS.into(),
                spec_version: 2_001_100,
                transaction_version: 4,
                profile: crate::profile::NAME.into(),
                max_dust: 10u128.pow(22),
            };
            let node = Node::connect(
                &setting("NOCTIUM_RELAY_NODE")?,
                policy.clone(),
                Duration::from_secs(15),
                64 * 1024 * 1024,
                10_000,
            )?;
            let mut seed = [0; 32];
            seed[31] = 1;
            node.attach_dust_seed(&seed)?;
            let dust = cache.dust().await?;
            let dust_parameters = cache.parameters(dust.k()).await?;
            let relay_parameters = cache.parameters(relay_circuit.k()).await?;
            let destination_parameters = cache.parameters(destination_circuit.k()).await?;
            let ttl = node.sync()?.block.tblock.to_secs() + 1800;
            let relay_target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![relay_bundle])?,
                br#"{"state":{}}"#,
                ttl,
                &mut OsRng,
            )?;
            let destination_target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![destination_bundle])?,
                br#"{"state":{"pot":[]}}"#,
                ttl,
                &mut OsRng,
            )?;
            let relay = relay_target.operation("forward", &relay_parameters, ttl)?;
            let destination =
                destination_target.operation("receive", &destination_parameters, ttl)?;
            let make_funding = || {
                DevelopmentFunding::new(
                    &node,
                    &dust,
                    &dust_parameters,
                    FeePolicy {
                        max_dust: policy.max_dust,
                        margin_blocks: 3,
                        max_spends: 8,
                    },
                    StdRng::from_entropy(),
                )
            };
            let make_signer = || {
                let approve =
                    |_: &UnsealedTransaction, candidate: &NetworkPolicy| *candidate == policy;
                ExplicitSeal::new(approve, StdRng::from_entropy())
            };
            let (.., relay_deploy_intent) = relay_target
                .deployment_intent()
                .prove(
                    CONTRACT_SEGMENT,
                    builtin_zkir::LocalProvingProvider {
                        rng: StdRng::from_entropy(),
                        resolver: &dust,
                        params: &dust_parameters,
                    },
                    &node.sync()?.state.parameters.cost_model.runtime_cost_model,
                )
                .await
                .map_err(|error| anyhow::anyhow!("Relay deployment proof: {error:?}"))?;
            let relay_deploy = BoundTransaction::prepare(
                &relay_deploy_intent,
                policy.clone(),
                &node,
                &make_funding(),
                &make_signer(),
            )
            .await?;
            let relay_receipt = finalize(&node, &relay_deploy).await?;
            let relay_current = relay_target
                .deployment_binding("forward")?
                .admit_committed_state(
                    &relay_receipt.contract_state,
                    relay_deploy.expected_state(),
                    &relay_receipt.finalized_hash,
                    true,
                )?;

            let (.., destination_deploy_intent) = destination_target
                .deployment_intent()
                .prove(
                    CONTRACT_SEGMENT,
                    builtin_zkir::LocalProvingProvider {
                        rng: StdRng::from_entropy(),
                        resolver: &dust,
                        params: &dust_parameters,
                    },
                    &node.sync()?.state.parameters.cost_model.runtime_cost_model,
                )
                .await
                .map_err(|error| anyhow::anyhow!("Destination deployment proof: {error:?}"))?;
            let destination_deploy = BoundTransaction::prepare(
                &destination_deploy_intent,
                policy.clone(),
                &node,
                &make_funding(),
                &make_signer(),
            )
            .await?;
            let destination_receipt = finalize(&node, &destination_deploy).await?;
            let destination_current = destination_target
                .deployment_binding("receive")?
                .admit_committed_state(
                    &destination_receipt.contract_state,
                    destination_deploy.expected_state(),
                    &destination_receipt.finalized_hash,
                    true,
                )?;

            let relay_address = contract_address(relay_target.contract_address())?;
            let destination_address = contract_address(destination_target.contract_address())?;
            let domain = HashOutput([0x28; 32]);
            let mut fixture_rng = StdRng::from_seed([0x28; 32]);
            let mint = Info::new(
                &mut fixture_rng,
                RELAY_AMOUNT,
                relay_address.custom_shielded_token_type(domain),
            );
            let opening = Fr::from(0x228u64);
            let mut relay_current = Some(relay_current);
            let mut destination_current = Some(destination_current);
            let make_inputs = || inputs(domain, &mint, destination_address, opening);

            let mut wrong_recipient = make_inputs();
            wrong_recipient.insert("recipient".into(), bytes32(HashOutput([0x99; 32])));
            ensure!(
                make_funding()
                    .bind_shielded_immediate_relay(
                        &relay,
                        &mut relay_current,
                        wrong_recipient,
                        &relay_parameters,
                        &destination,
                        &mut destination_current,
                        &destination_parameters,
                        &cache,
                        &make_signer(),
                        StdRng::from_entropy(),
                    )
                    .await
                    .is_err(),
                "wrong destination address was accepted"
            );
            ensure!(relay_current.is_some() && destination_current.is_some());
            let mut wrong_color = make_inputs();
            wrong_color.insert("color".into(), bytes32(HashOutput([0x77; 32])));
            ensure!(
                make_funding()
                    .bind_shielded_immediate_relay(
                        &relay,
                        &mut relay_current,
                        wrong_color,
                        &relay_parameters,
                        &destination,
                        &mut destination_current,
                        &destination_parameters,
                        &cache,
                        &make_signer(),
                        StdRng::from_entropy(),
                    )
                    .await
                    .is_err(),
                "mismatched relay color was accepted"
            );
            ensure!(relay_current.is_some() && destination_current.is_some());

            let bound = make_funding()
                .bind_shielded_immediate_relay(
                    &relay,
                    &mut relay_current,
                    make_inputs(),
                    &relay_parameters,
                    &destination,
                    &mut destination_current,
                    &destination_parameters,
                    &cache,
                    &make_signer(),
                    StdRng::from_entropy(),
                )
                .await
                .context("prepare Relay.forward and Destination.receive")?;
            ensure!(relay_current.is_none() && destination_current.is_none());
            let receipt = finalize(&node, &bound).await?;
            ensure!(receipt.contract_address == hex::encode(relay_address.0.0));
            ensure!(
                bound.contract_event_counts()
                    == BTreeMap::from([
                        (hex::encode(relay_address.0.0), 1),
                        (hex::encode(destination_address.0.0), 1),
                    ]),
                "Relay and Destination calls were not both committed"
            );
            ensure!(receipt.contract_state == relay_receipt.contract_state);
            let destination_bytes = receipt
                .secondary_states
                .get(&hex::encode(destination_address.0.0))
                .context("Destination state missing from finalized receipt")?;
            let destination_state: ContractState<Db> = native_decode(destination_bytes)?;
            let output_coin =
                mint.evolve_from(b"midnight:kernel:nonce_evolve", mint.value, mint.type_);
            let output_commitment =
                output_coin.commitment(&CoinRecipient::Contract(destination_address));
            let qualified = map_coin_by_nonce(&destination_state, output_coin.nonce)?;
            ensure!(qualified.nonce == output_coin.nonce);
            ensure!(qualified.type_ == output_coin.type_ && qualified.value == RELAY_AMOUNT);

            let final_snapshot = node.sync()?;
            ensure!(final_snapshot.validate(&policy).is_ok());
            let output_index = tree_index(&final_snapshot, output_commitment, destination_address)?;
            let relay_commitment = mint.commitment(&CoinRecipient::Contract(relay_address));
            let relay_nullifier = mint.nullifier(&SenderEvidence::Contract(relay_address));
            let transient_index = tree_index(&final_snapshot, relay_commitment, relay_address)?;
            ensure!(
                qualified.mt_index == output_index,
                "Destination Map index differs from Ledger"
            );
            ensure!(
                final_snapshot
                    .state
                    .zswap
                    .nullifiers
                    .contains_key(&relay_nullifier),
                "Relay transient nullifier was not recorded"
            );
            ensure!(
                bound.expected_state() == receipt.contract_state
                    && bound
                        .secondary_states()
                        .get(&hex::encode(destination_address.0.0))
                        == Some(destination_bytes),
                "receipt states differ from prepared composition bindings"
            );
            println!(
                "{}",
                json!({
                    "relayDeploymentHeight": relay_receipt.height,
                    "destinationDeploymentHeight": destination_receipt.height,
                    "callHeight": receipt.height,
                    "callTransaction": receipt.transaction_id,
                    "relayAddress": hex::encode(relay_address.0.0),
                    "destinationAddress": hex::encode(destination_address.0.0),
                    "domain": hex::encode(domain.0),
                    "transientCommitment": hex::encode(relay_commitment.0.0),
                    "transientIndex": transient_index,
                    "nullifier": hex::encode(relay_nullifier.0.0),
                    "outputCommitment": hex::encode(output_commitment.0.0),
                    "outputIndex": output_index,
                    "value": qualified.value.to_string(),
                    "rejected": ["wrongRecipient", "wrongColor"]
                })
            );
            Ok(())
        })
    }
}
