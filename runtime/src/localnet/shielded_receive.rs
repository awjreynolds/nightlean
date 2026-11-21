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
use transient_crypto::{commitment::PedersenRandomness, proofs::Proof};
use zswap::{Offer, Output, prove::ZswapResolver};

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
        funding::{CONTRACT_SEGMENT, FeePolicy, UnsealedTransaction},
        localnet::{ExplicitSeal, Node, native_decode},
        proof::WitnessContractTarget,
        zkir::IrSource,
    };
    use anyhow::{Context, Result, ensure};
    use base_crypto::fab::AlignedValue;
    use coin_structure::transfer::Recipient;
    use onchain_runtime::state::{ContractState, StateValue};
    use rand::{SeedableRng, rngs::OsRng};
    use serde_json::json;
    use std::{
        env,
        path::Path,
        thread,
        time::{Duration, Instant},
    };
    use storage::arena::Sp;
    use transient_crypto::proofs::Zkir;

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
}
