use super::{DEVELOPMENT_GENESIS, DevelopmentFunding, Error, ProofCache, Result, check};
use crate::{
    Db,
    client::{BoundTransaction, HostFailure, SigningAdapter, Snapshot},
    proof::{
        ContractOperationTarget, ContractStateBinding, CurrentStateContext, LocalProver,
        PreparedProof, TrustedParameters,
    },
};
use base_crypto::{hash::HashOutput, rng::SplittableRng};
use coin_structure::{
    coin::{Commitment, Info},
    contract::ContractAddress,
};
use ledger::structure::GUARANTEED_SEGMENT;
use rand::rngs::StdRng;
use serde_json::Value;
use std::{collections::BTreeMap, future::pending};
use transient_crypto::{
    commitment::PedersenRandomness,
    proofs::{Proof, ProofPreimage},
};
use zswap::{Input, Offer, Output, prove::ZswapResolver};

pub(super) struct BookedOffer {
    pub(super) offer: Offer<Proof, Db>,
    pub(super) randomness: PedersenRandomness,
    address: ContractAddress,
    commitment: Commitment,
    index: u64,
    current_state: Vec<u8>,
}

impl BookedOffer {
    pub(super) fn check_booking(
        &self,
        snapshot: &Snapshot,
    ) -> std::result::Result<(), HostFailure> {
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&self.offer, None)
            .map_err(|_| HostFailure)?;
        let state = snapshot
            .state
            .contract
            .get(&self.address)
            .ok_or(HostFailure)?;
        let mut bytes = Vec::new();
        serialize::tagged_serialize(&*state, &mut bytes).map_err(|_| HostFailure)?;
        if indices.get(&self.commitment).as_deref() != Some(&self.index)
            || bytes != self.current_state
        {
            return Err(HostFailure);
        }
        Ok(())
    }
}

pub(super) struct BookedWalletOffer {
    pub(super) offer: Offer<Proof, Db>,
    pub(super) randomness: PedersenRandomness,
    address: ContractAddress,
    commitment: Commitment,
    index: u64,
    current_state: Vec<u8>,
}

impl BookedWalletOffer {
    pub(super) fn check_booking(
        &self,
        snapshot: &Snapshot,
    ) -> std::result::Result<(), HostFailure> {
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&self.offer, None)
            .map_err(|_| HostFailure)?;
        let state = snapshot
            .state
            .contract
            .get(&self.address)
            .ok_or(HostFailure)?;
        let mut bytes = Vec::new();
        serialize::tagged_serialize(&*state, &mut bytes).map_err(|_| HostFailure)?;
        let zswap = &snapshot.state.zswap;
        let Some(input) = self.offer.inputs.get(0) else {
            return Err(HostFailure);
        };
        let Some(output) = self.offer.outputs.get(0) else {
            return Err(HostFailure);
        };
        if bytes != self.current_state
            || indices.get(&self.commitment).as_deref() != Some(&self.index)
            || !zswap.past_roots.contains(&input.merkle_tree_root)
            || zswap.nullifiers.contains_key(&input.nullifier)
            || self.offer.inputs.len() != 1
            || self.offer.outputs.len() != 1
            || !self.offer.transient.is_empty()
            || input.contract_address.is_some()
            || output.coin_com != self.commitment
            || output.contract_address.as_deref() != Some(&self.address)
            || output.ciphertext.is_some()
        {
            return Err(HostFailure);
        }
        Ok(())
    }
}

impl DevelopmentFunding<'_> {
    /// Bind one mint-funded contract-owned output from the development chain's
    /// current Zswap state. The caller approves the complete transaction before sealing.
    pub async fn bind_minted_shielded_receive(
        self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        coin: &Info,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        rng: StdRng,
    ) -> Result<BoundTransaction> {
        self.bind_minted_shielded_receive_with_binding(
            target, current, inputs, coin, parameters, cache, signer, rng,
        )
        .await
        .map(|(bound, _)| bound)
    }

    /// Bind one wallet-owned input into one contract-owned Map coin.
    /// The caller builds the input with its wallet SDK. This method receives only the
    /// proof preimage, never wallet keys or wallet state.
    pub async fn bind_wallet_shielded_receive(
        mut self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        coin: &Info,
        input: Input<ProofPreimage, Db>,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        mut rng: StdRng,
    ) -> Result<BoundTransaction> {
        let policy = self.node.policy.clone();
        check(policy.genesis == DEVELOPMENT_GENESIS, Error::Policy)?;
        check(
            coin.value > 0 && coin.value <= i128::MAX as u128,
            Error::State,
        )?;
        check(input.contract_address.is_none(), Error::State)?;
        check(input.segment() == Some(GUARANTEED_SEGMENT), Error::State)?;

        let input_delta = input.delta();
        let bytes = hex::decode(
            target
                .contract_address()
                .strip_prefix("0x")
                .unwrap_or(target.contract_address()),
        )
        .map_err(|_| Error::State)?;
        let address = ContractAddress(HashOutput(bytes.try_into().map_err(|_| Error::State)?));
        let snapshot = self.node.sync()?;
        snapshot.validate(&policy).map_err(|_| Error::Network)?;
        check(policy == self.node.policy, Error::Policy)?;

        let output =
            Output::<_, Db>::new_contract_owned(&mut rng, coin, Some(GUARANTEED_SEGMENT), address)
                .map_err(|_| Error::State)?;
        let output_delta = output.delta();
        check(
            input_delta.token_type == output_delta.token_type
                && input_delta.value.checked_neg() == Some(output_delta.value),
            Error::State,
        )?;
        let commitment = output.coin_com;
        let offer = Offer::new(vec![input], vec![output], vec![]).ok_or(Error::State)?;
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&offer, None)
            .map_err(|_| Error::State)?;
        let index = *indices.get(&commitment).ok_or(Error::State)?;

        let prepared = PreparedProof::from_contract_witness_inputs_with_com_indices(
            target, current, inputs, indices, &mut rng,
        )
        .map_err(|_| Error::Proof)?;
        let proved = prepared
            .prove(
                &LocalProver::new(rng.split()),
                parameters,
                1_048_576,
                pending(),
            )
            .await
            .map_err(|_| Error::Proof)?;
        let binding = proved.contract_binding().ok_or(Error::State)?;
        let current_state = binding.current_state_bytes().ok_or(Error::State)?.to_vec();

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
        self.wallet_shielded_receive = Some(BookedWalletOffer {
            offer,
            randomness,
            address,
            commitment,
            index,
            current_state,
        });
        let expected = &self
            .wallet_shielded_receive
            .as_ref()
            .ok_or(Error::State)?
            .offer;
        let bound = BoundTransaction::prepare_wallet_shielded_receive(
            proved.native(),
            expected,
            policy,
            self.node,
            &self,
            signer,
        )
        .await
        .map_err(|_| Error::State)?;
        check(
            bound.expected_state() == binding.expected_state(),
            Error::State,
        )?;
        Ok(bound)
    }

    pub(crate) async fn bind_minted_shielded_receive_with_binding(
        mut self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        coin: &Info,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        mut rng: StdRng,
    ) -> Result<(BoundTransaction, ContractStateBinding)> {
        let policy = self.node.policy.clone();
        check(policy.genesis == DEVELOPMENT_GENESIS, Error::Policy)?;
        check(
            coin.value > 0 && coin.value <= u128::from(u64::MAX),
            Error::State,
        )?;
        let bytes = hex::decode(target.contract_address()).map_err(|_| Error::State)?;
        let address = ContractAddress(HashOutput(bytes.try_into().map_err(|_| Error::State)?));
        let snapshot = self.node.sync()?;
        snapshot.validate(&policy).map_err(|_| Error::Network)?;
        let output =
            Output::<_, Db>::new_contract_owned(&mut rng, coin, Some(GUARANTEED_SEGMENT), address)
                .map_err(|_| Error::State)?;
        let commitment = output.coin_com;
        let offer = Offer::new(vec![], vec![output], vec![]).ok_or(Error::State)?;
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&offer, None)
            .map_err(|_| Error::State)?;
        let index = *indices.get(&commitment).ok_or(Error::State)?;
        let prepared = PreparedProof::from_contract_witness_inputs_with_com_indices(
            target, current, inputs, indices, &mut rng,
        )
        .map_err(|_| Error::State)?;
        let proved = prepared
            .prove(
                &LocalProver::new(rng.split()),
                parameters,
                1_048_576,
                pending(),
            )
            .await
            .map_err(|_| Error::Proof)?;
        let binding = proved.contract_binding().ok_or(Error::State)?;
        let current_state = binding.current_state_bytes().ok_or(Error::State)?.to_vec();

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
        self.shielded_receive = Some(BookedOffer {
            offer,
            randomness,
            address,
            commitment,
            index,
            current_state,
        });
        let expected = &self.shielded_receive.as_ref().ok_or(Error::State)?.offer;
        let bound = BoundTransaction::prepare_shielded_receive(
            proved.native(),
            expected,
            policy,
            self.node,
            &self,
            signer,
        )
        .await
        .map_err(|_| Error::State)?;
        check(
            bound.expected_state() == binding.expected_state(),
            Error::State,
        )?;
        Ok((bound, binding.clone()))
    }
}

#[cfg(all(test, feature = "zkir-321"))]
mod tests {
    use super::*;
    use crate::{
        artifacts::{self, ContractBundleSet, Role},
        client::{ChainAdapter, FinalizedReceipt, NetworkPolicy, Submission},
        funding::{CONTRACT_SEGMENT, FeePolicy, SealedTransaction, UnsealedTransaction},
        localnet::{ExplicitSeal, Node, native_decode},
        proof::WitnessContractTarget,
        zkir::IrSource,
    };
    use anyhow::{Context, Result, ensure};
    use base_crypto::fab::AlignedValue;
    use coin_structure::transfer::{Recipient, SenderEvidence};
    use ledger::structure::Transaction;
    use onchain_runtime::state::{ContractState, StateValue};
    use rand::{SeedableRng, rngs::OsRng};
    use serde_json::json;
    use std::{
        borrow::Cow,
        env,
        path::Path,
        thread,
        time::{Duration, Instant},
    };
    use storage::arena::Sp;
    use transient_crypto::{
        merkle_tree::MerkleTreeCollapsedUpdate,
        proofs::{Proof, Zkir},
    };
    use zswap::{Offer, keys::SecretKeys, local::State as WalletState};

    async fn finalize(node: &Node, bound: &BoundTransaction) -> Result<FinalizedReceipt> {
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

    fn offer_from_bound(bound: &BoundTransaction) -> Result<Offer<Proof, Db>> {
        let sealed: SealedTransaction = serialize::tagged_deserialize(bound.bytes())?;
        let Transaction::Standard(transaction) = sealed else {
            anyhow::bail!("expected a standard transaction")
        };
        transaction
            .guaranteed_coins
            .as_deref()
            .cloned()
            .context("missing guaranteed shielded offer")
    }

    #[test]
    #[ignore = "requires a generated funded receive bundle and isolated development node"]
    fn funded_shielded_receive_localnet() -> Result<()> {
        futures::executor::block_on(async {
            let setting = |name| env::var(name).with_context(|| format!("missing {name}"));
            let bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_RECEIVE_BUNDLE")?),
                Some(&setting("NOCTIUM_RECEIVE_MANIFEST_SHA256")?),
            )?;
            let circuit = IrSource::load(bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_RECEIVE_PARAMETER_CACHE")?.into(),
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
                &setting("NOCTIUM_RECEIVE_NODE")?,
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
            let parameters = cache.parameters(circuit.k()).await?;
            let ttl = node.sync()?.block.tblock.to_secs() + 1800;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![bundle])?,
                br#"{"state":{"pot":[]}}"#,
                ttl,
                &mut OsRng,
            )?;
            let operation = target.operation("tip", &parameters, ttl)?;
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
            let approve = |_: &UnsealedTransaction, candidate: &NetworkPolicy| *candidate == policy;
            let signer = ExplicitSeal::new(approve, StdRng::from_entropy());
            let (_, deploy) = target
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
                .map_err(|error| anyhow::anyhow!("{error:?}"))?;
            let deploy =
                BoundTransaction::prepare(&deploy, policy.clone(), &node, &make_funding(), &signer)
                    .await?;
            let deployed = finalize(&node, &deploy).await?;
            let current = target.deployment_binding("tip")?.admit_committed_state(
                &deployed.contract_state,
                deploy.expected_state(),
                &deployed.finalized_hash,
                true,
            )?;
            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("wrong contract address size"))?,
            ));
            let domain = HashOutput([3; 32]);
            let coin = Info::new(&mut OsRng, 5, address.custom_shielded_token_type(domain));
            let snapshot = node.sync()?;
            let index = snapshot.state.zswap.first_free;
            let commitment = coin.commitment(&Recipient::Contract(address));
            let inputs = || {
                BTreeMap::from([
                    ("domain".into(), json!({"kind":"bytes", "values":domain.0})),
                    (
                        "nonce".into(),
                        json!({"kind":"bytes", "values":coin.nonce.0.0}),
                    ),
                    (
                        "color".into(),
                        json!({"kind":"bytes", "values":coin.type_.0.0}),
                    ),
                ])
            };
            let mut absent = Some(current);
            ensure!(
                operation
                    .prepare_call(&mut absent, &parameters, inputs(), &mut OsRng)
                    .is_err(),
                "receive without offer prepared"
            );
            let current = absent.context("missing offer consumed the current state")?;
            let other_coin = Info::new(&mut OsRng, coin.value, coin.type_);
            let signer = ExplicitSeal::new(approve, StdRng::from_entropy());
            ensure!(
                make_funding()
                    .bind_minted_shielded_receive(
                        &operation,
                        &current,
                        inputs(),
                        &other_coin,
                        &parameters,
                        &cache,
                        &signer,
                        StdRng::from_entropy(),
                    )
                    .await
                    .is_err(),
                "mismatched offer bound a transaction"
            );
            ensure!(
                node.finalized_contract_state(target.contract_address())?
                    .bytes
                    == deployed.contract_state,
                "invalid offer changed the Map"
            );
            let bound = make_funding()
                .bind_minted_shielded_receive(
                    &operation,
                    &current,
                    inputs(),
                    &coin,
                    &parameters,
                    &cache,
                    &signer,
                    StdRng::from_entropy(),
                )
                .await?;
            let receipt = finalize(&node, &bound).await?;
            let state: ContractState<Db> = native_decode(&receipt.contract_state)?;
            let StateValue::Array(slots) = state.data.get_ref() else {
                anyhow::bail!("expected native state array");
            };
            let Some(StateValue::Map(coins)) = slots.get(0) else {
                anyhow::bail!("expected coin Map in slot 0");
            };
            ensure!(
                coins.get(&AlignedValue::from(coin.nonce)).as_deref()
                    == Some(&StateValue::Cell(Sp::new(AlignedValue::from(
                        coin.qualify(index)
                    )))),
                "finalized Map does not contain the Ledger-assigned qualified coin"
            );
            ensure!(
                node.sync()?
                    .state
                    .zswap
                    .coin_coms_set
                    .contains_key(&commitment)
            );
            println!(
                "{}",
                json!({
                    "deploymentHeight": deployed.height,
                    "callHeight": receipt.height,
                    "callTransaction": receipt.transaction_id,
                    "contractAddress": receipt.contract_address,
                    "commitment": hex::encode(commitment.0.0),
                    "nonce": hex::encode(coin.nonce.0.0),
                    "color": hex::encode(coin.type_.0.0),
                    "value": coin.value.to_string(),
                    "mtIndex": index,
                    "stateSha256": artifacts::digest(&receipt.contract_state),
                    "k": circuit.k(),
                    "rejected": ["missingOffer", "mismatchedOffer"]
                })
            );
            Ok(())
        })
    }

    #[test]
    #[ignore = "requires generated receive and whole-spend bundles and an isolated development node"]
    fn funded_wallet_shielded_receive_localnet() -> Result<()> {
        futures::executor::block_on(async {
            let setting = |name| env::var(name).with_context(|| format!("missing {name}"));
            let deposit_bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_WALLET_RECEIVE_DEPOSIT_BUNDLE")?),
                Some(&setting("NOCTIUM_WALLET_RECEIVE_DEPOSIT_MANIFEST_SHA256")?),
            )?;
            let seed_tip_bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_WALLET_RECEIVE_SEED_TIP_BUNDLE")?),
                Some(&setting("NOCTIUM_WALLET_RECEIVE_SEED_TIP_MANIFEST_SHA256")?),
            )?;
            let seed_spend_bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_WALLET_RECEIVE_SEED_SPEND_BUNDLE")?),
                Some(&setting(
                    "NOCTIUM_WALLET_RECEIVE_SEED_SPEND_MANIFEST_SHA256",
                )?),
            )?;
            let deposit_circuit = IrSource::load(deposit_bundle.file(Role::Circuit)?)?;
            let seed_tip_circuit = IrSource::load(seed_tip_bundle.file(Role::Circuit)?)?;
            let seed_spend_circuit = IrSource::load(seed_spend_bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_WALLET_RECEIVE_PARAMETER_CACHE")?.into(),
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
                &setting("NOCTIUM_WALLET_RECEIVE_NODE")?,
                policy.clone(),
                Duration::from_secs(15),
                64 * 1024 * 1024,
                10_000,
            )?;
            let mut dust_seed = [0; 32];
            dust_seed[31] = 1;
            node.attach_dust_seed(&dust_seed)?;
            let dust = cache.dust().await?;
            let dust_parameters = cache.parameters(dust.k()).await?;
            let deposit_parameters = cache.parameters(deposit_circuit.k()).await?;
            let seed_tip_parameters = cache.parameters(seed_tip_circuit.k()).await?;
            let seed_spend_parameters = cache.parameters(seed_spend_circuit.k()).await?;
            let ttl = node.sync()?.block.tblock.to_secs() + 1800;
            let deposit_target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![deposit_bundle])?,
                br#"{"state":{"pot":[]}}"#,
                ttl,
                &mut OsRng,
            )?;
            let seed_target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![seed_tip_bundle, seed_spend_bundle])?,
                br#"{"state":{"pot":[]}}"#,
                ttl,
                &mut OsRng,
            )?;
            let deposit = deposit_target.operation("tip", &deposit_parameters, ttl)?;
            let seed_tip = seed_target.operation("tip", &seed_tip_parameters, ttl)?;
            let seed_spend = seed_target.operation("spend", &seed_spend_parameters, ttl)?;
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
            let approve = |_: &UnsealedTransaction, candidate: &NetworkPolicy| *candidate == policy;
            let make_signer = || ExplicitSeal::new(approve, StdRng::from_entropy());

            let seed_snapshot = node.sync()?;
            let (_, seed_deploy_intent) = seed_target
                .deployment_intent()
                .prove(
                    CONTRACT_SEGMENT,
                    builtin_zkir::LocalProvingProvider {
                        rng: StdRng::from_entropy(),
                        resolver: &dust,
                        params: &dust_parameters,
                    },
                    &seed_snapshot.state.parameters.cost_model.runtime_cost_model,
                )
                .await
                .map_err(|error| anyhow::anyhow!("seed deployment proof: {error:?}"))?;
            let seed_deploy = BoundTransaction::prepare(
                &seed_deploy_intent,
                policy.clone(),
                &node,
                &make_funding(),
                &make_signer(),
            )
            .await?;
            let seed_deployed = finalize(&node, &seed_deploy)
                .await
                .context("finalize seed contract")?;
            let mut seed_current = seed_target
                .deployment_binding("tip")?
                .admit_committed_state(
                    &seed_deployed.contract_state,
                    seed_deploy.expected_state(),
                    &seed_deployed.finalized_hash,
                    true,
                )?;

            let deposit_snapshot = node.sync()?;
            let (_, deposit_deploy_intent) = deposit_target
                .deployment_intent()
                .prove(
                    CONTRACT_SEGMENT,
                    builtin_zkir::LocalProvingProvider {
                        rng: StdRng::from_entropy(),
                        resolver: &dust,
                        params: &dust_parameters,
                    },
                    &deposit_snapshot
                        .state
                        .parameters
                        .cost_model
                        .runtime_cost_model,
                )
                .await
                .map_err(|error| anyhow::anyhow!("deposit deployment proof: {error:?}"))?;
            let deposit_deploy = BoundTransaction::prepare(
                &deposit_deploy_intent,
                policy.clone(),
                &node,
                &make_funding(),
                &make_signer(),
            )
            .await?;
            let deposit_deployed = finalize(&node, &deposit_deploy)
                .await
                .context("finalize deposit contract")?;
            let deposit_current = deposit_target
                .deployment_binding("tip")?
                .admit_committed_state(
                    &deposit_deployed.contract_state,
                    deposit_deploy.expected_state(),
                    &deposit_deployed.finalized_hash,
                    true,
                )?;
            let seed_address = ContractAddress(HashOutput(
                hex::decode(
                    seed_target
                        .contract_address()
                        .strip_prefix("0x")
                        .unwrap_or(seed_target.contract_address()),
                )?
                .try_into()
                .map_err(|_| anyhow::anyhow!("wrong seed contract address size"))?,
            ));
            let deposit_address = ContractAddress(HashOutput(
                hex::decode(
                    deposit_target
                        .contract_address()
                        .strip_prefix("0x")
                        .unwrap_or(deposit_target.contract_address()),
                )?
                .try_into()
                .map_err(|_| anyhow::anyhow!("wrong deposit contract address size"))?,
            ));

            let mut shielded_rng = StdRng::from_entropy();
            let domain = HashOutput([0x42; 32]);
            let seed_coin = Info::new(
                &mut shielded_rng,
                5,
                seed_address.custom_shielded_token_type(domain),
            );
            let pre_seed_snapshot = node.sync()?;
            let seed_index = pre_seed_snapshot.state.zswap.first_free;
            let mut wallet_state = WalletState::<Db>::new();
            if seed_index > 0 {
                let update = MerkleTreeCollapsedUpdate::new(
                    &pre_seed_snapshot.state.zswap.coin_coms,
                    0,
                    seed_index - 1,
                )
                .context("build initial wallet Merkle sync")?;
                wallet_state = wallet_state
                    .apply_collapsed_update(&update)
                    .context("apply initial wallet Merkle sync")?;
            }
            let seed_tip_inputs = || {
                BTreeMap::from([
                    ("domain".into(), json!({"kind":"bytes", "values":domain.0})),
                    (
                        "nonce".into(),
                        json!({"kind":"bytes", "values":seed_coin.nonce.0.0}),
                    ),
                    (
                        "color".into(),
                        json!({"kind":"bytes", "values":seed_coin.type_.0.0}),
                    ),
                ])
            };
            let (seed_tip_bound, seed_tip_binding) = make_funding()
                .bind_minted_shielded_receive_with_binding(
                    &seed_tip,
                    &seed_current,
                    seed_tip_inputs(),
                    &seed_coin,
                    &seed_tip_parameters,
                    &cache,
                    &make_signer(),
                    StdRng::from_entropy(),
                )
                .await
                .context("bind whole-spend seed coin")?;
            let seed_tip_receipt = finalize(&node, &seed_tip_bound)
                .await
                .context("finalize whole-spend seed coin")?;
            seed_current = seed_tip_binding.admit_committed_state(
                &seed_tip_receipt.contract_state,
                seed_tip_bound.expected_state(),
                &seed_tip_receipt.finalized_hash,
                false,
            )?;

            let wallet_keys = SecretKeys::from_rng_seed(&mut shielded_rng);
            let wallet_public_key = wallet_keys.coin_public_key();
            let wallet_encryption_key = wallet_keys.enc_public_key();
            let wallet_output_index = node.sync()?.state.zswap.first_free;
            let spend_inputs = BTreeMap::from([
                (
                    "nonce".into(),
                    json!({"kind":"bytes", "values":seed_coin.nonce.0.0}),
                ),
                (
                    "recipient".into(),
                    json!({"kind":"bytes", "values":wallet_public_key.0.0}),
                ),
            ]);
            let seed_spend_bound = make_funding()
                .bind_shielded_map_spend(
                    &seed_spend,
                    &seed_current,
                    spend_inputs,
                    wallet_encryption_key,
                    &seed_spend_parameters,
                    &cache,
                    &make_signer(),
                    StdRng::from_entropy(),
                )
                .await
                .context("spend seed coin to ephemeral wallet")?;
            finalize(&node, &seed_spend_bound)
                .await
                .context("finalize seed spend")?;

            let seed_info = Info::from(&seed_coin.qualify(seed_index));
            let wallet_coin = seed_info.evolve_from(
                b"midnight:kernel:nonce_evolve",
                seed_coin.value,
                seed_coin.type_,
            );
            let tip_offer = offer_from_bound(&seed_tip_bound)?;
            let spend_offer = offer_from_bound(&seed_spend_bound)?;
            let wallet_state = wallet_state
                .apply(&wallet_keys, &tip_offer)
                .context("apply seed receive to ephemeral wallet state")?
                .apply(&wallet_keys, &spend_offer)
                .context("apply whole spend to ephemeral wallet state")?;
            let wallet_nullifier = wallet_coin.nullifier(&SenderEvidence::User(Cow::Borrowed(
                &wallet_keys.coin_secret_key,
            )));
            let wallet_qualified = wallet_state
                .coins
                .get(&wallet_nullifier)
                .map(|qualified| *qualified)
                .context("whole spend output missing from ephemeral wallet state")?;
            ensure!(
                wallet_qualified == wallet_coin.qualify(wallet_output_index),
                "wallet state assigned the wrong output index"
            );
            let (_, mismatched_input) = wallet_state
                .spend(
                    &mut shielded_rng,
                    &wallet_keys,
                    &wallet_qualified,
                    Some(GUARANTEED_SEGMENT),
                )
                .context("prepare mismatch input from ephemeral wallet")?;
            let mut mismatched_coin = wallet_coin;
            mismatched_coin.value += 1;
            ensure!(
                make_funding()
                    .bind_wallet_shielded_receive(
                        &deposit,
                        &deposit_current,
                        BTreeMap::from([
                            (
                                "nonce".into(),
                                json!({"kind":"bytes", "values":wallet_coin.nonce.0.0}),
                            ),
                            (
                                "color".into(),
                                json!({"kind":"bytes", "values":wallet_coin.type_.0.0}),
                            ),
                            ("amount".into(), json!(wallet_coin.value.to_string()),),
                        ]),
                        &mismatched_coin,
                        mismatched_input,
                        &deposit_parameters,
                        &cache,
                        &make_signer(),
                        StdRng::from_entropy(),
                    )
                    .await
                    .is_err(),
                "unequal-value wallet offer bound a receive"
            );
            ensure!(
                node.finalized_contract_state(deposit_target.contract_address())?
                    .bytes
                    == deposit_deployed.contract_state,
                "mismatched wallet offer changed the receive Map"
            );

            let (_, input) = wallet_state
                .spend(
                    &mut shielded_rng,
                    &wallet_keys,
                    &wallet_qualified,
                    Some(GUARANTEED_SEGMENT),
                )
                .context("prepare wallet input")?;
            let input_nullifier = input.nullifier;
            let receive_index = node.sync()?.state.zswap.first_free;
            let receive_commitment = wallet_coin.commitment(&Recipient::Contract(deposit_address));
            let inputs = || {
                BTreeMap::from([
                    (
                        "nonce".into(),
                        json!({"kind":"bytes", "values":wallet_coin.nonce.0.0}),
                    ),
                    (
                        "color".into(),
                        json!({"kind":"bytes", "values":wallet_coin.type_.0.0}),
                    ),
                    ("amount".into(), json!(wallet_coin.value.to_string())),
                ])
            };
            let bound = make_funding()
                .bind_wallet_shielded_receive(
                    &deposit,
                    &deposit_current,
                    inputs(),
                    &wallet_coin,
                    input,
                    &deposit_parameters,
                    &cache,
                    &make_signer(),
                    StdRng::from_entropy(),
                )
                .await
                .context("bind wallet-funded shielded receive")?;
            let receipt = finalize(&node, &bound)
                .await
                .context("finalize wallet-funded shielded receive")?;
            let state: ContractState<Db> = native_decode(&receipt.contract_state)?;
            let StateValue::Array(slots) = state.data.get_ref() else {
                anyhow::bail!("expected native receive state array")
            };
            let Some(StateValue::Map(coins)) = slots.get(0) else {
                anyhow::bail!("expected receive coin Map in slot 0")
            };
            ensure!(
                coins.get(&AlignedValue::from(wallet_coin.nonce)).as_deref()
                    == Some(&StateValue::Cell(Sp::new(AlignedValue::from(
                        wallet_coin.qualify(receive_index)
                    )))),
                "wallet receive Map entry lacks the Ledger-assigned output index"
            );
            let final_snapshot = node.sync()?;
            let (leaf, owner) = final_snapshot
                .state
                .zswap
                .coin_coms
                .index(receive_index)
                .context("wallet receive output leaf missing")?;
            ensure!(
                leaf == receive_commitment.0 && owner.as_deref() == Some(&deposit_address),
                "wallet receive output commitment has the wrong owner"
            );
            ensure!(
                final_snapshot
                    .state
                    .zswap
                    .nullifiers
                    .contains_key(&input_nullifier),
                "wallet input nullifier missing after finalization"
            );

            let (_, replayed_input) = wallet_state
                .spend(
                    &mut shielded_rng,
                    &wallet_keys,
                    &wallet_qualified,
                    Some(GUARANTEED_SEGMENT),
                )
                .context("prepare replay input")?;
            ensure!(
                make_funding()
                    .bind_wallet_shielded_receive(
                        &deposit,
                        &deposit_current,
                        inputs(),
                        &wallet_coin,
                        replayed_input,
                        &deposit_parameters,
                        &cache,
                        &make_signer(),
                        StdRng::from_entropy(),
                    )
                    .await
                    .is_err(),
                "spent wallet input replay bound another receive"
            );
            ensure!(
                node.finalized_contract_state(deposit_target.contract_address())?
                    .bytes
                    == receipt.contract_state,
                "replayed wallet input changed the receive Map"
            );
            println!(
                "{}",
                json!({
                    "seedTipHeight": seed_tip_receipt.height,
                    "depositHeight": receipt.height,
                    "depositTransaction": receipt.transaction_id,
                    "inputNullifier": hex::encode(input_nullifier.0.0),
                    "outputCommitment": hex::encode(receive_commitment.0.0),
                    "outputIndex": receive_index,
                    "value": wallet_coin.value.to_string(),
                    "rejected": ["unequalValue", "replayedInput"]
                })
            );
            Ok(())
        })
    }
}
