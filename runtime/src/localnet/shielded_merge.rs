use super::{DEVELOPMENT_GENESIS, DevelopmentFunding, Error, ProofCache, Result, check};
use crate::{
    Db,
    client::{BoundTransaction, HostFailure, SigningAdapter, Snapshot},
    proof::{ContractOperationTarget, CurrentStateContext, LocalProver, PreparedProof, TrustedParameters},
};
use base_crypto::{fab::AlignedValue, hash::HashOutput, rng::SplittableRng};
use coin_structure::{
    coin::{Commitment, Info, Nonce, Nullifier, QualifiedInfo},
    contract::ContractAddress,
    transfer::{Recipient, SenderEvidence},
};
use ledger::structure::GUARANTEED_SEGMENT;
use onchain_runtime::state::{ContractState, StateValue};
use rand::rngs::StdRng;
use serde_json::Value;
use storage::storage::Map;
use std::{collections::BTreeMap, future::pending};
use transient_crypto::{commitment::PedersenRandomness, proofs::Proof};
use zswap::{Offer, prove::ZswapResolver};

use super::shielded_transfer::{
    stage_contract_owned_input, stage_contract_owned_output, stage_contract_owned_transient, StagedContractInput,
    StagedContractOutput,
};

struct BookedMergeInput {
    coin: QualifiedInfo,
    commitment: Commitment,
    nullifier: Nullifier,
    root: transient_crypto::merkle_tree::MerkleTreeDigest,
}

enum SecondMergeInput {
    Finalized(BookedMergeInput),
    Staged { coin: Info, domain: HashOutput },
}

pub(super) struct BookedMerge {
    pub(super) offer: Offer<Proof, Db>,
    pub(super) randomness: PedersenRandomness,
    address: ContractAddress,
    current_state: Vec<u8>,
    first: BookedMergeInput,
    second: SecondMergeInput,
    output: Commitment,
    indices: Map<Commitment, u64>,
}

impl BookedMerge {
    pub(super) fn staged_mint(&self) -> Option<(&Info, HashOutput)> {
        match &self.second {
            SecondMergeInput::Staged { coin, domain } => Some((coin, *domain)),
            SecondMergeInput::Finalized(_) => None,
        }
    }

    pub(super) fn check_booking(
        &self,
        snapshot: &Snapshot,
    ) -> std::result::Result<(), HostFailure> {
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&self.offer, None)
            .map_err(|_| HostFailure)?;
        let contract = snapshot
            .state
            .contract
            .get(&self.address)
            .ok_or(HostFailure)?;
        let current_state = tagged_state_bytes(&contract).map_err(|_| HostFailure)?;
        let zswap = &snapshot.state.zswap;
        let current_root = zswap.coin_coms.root().ok_or(HostFailure)?;
        let output = self.offer.outputs.get(0).ok_or(HostFailure)?;
        if current_state != self.current_state
            || self.offer.outputs.len() != 1
            || output.coin_com != self.output
            || output.contract_address.as_deref() != Some(&self.address)
            || output.ciphertext.is_some()
            || indices != self.indices
        {
            return Err(HostFailure);
        }
        let second = match &self.second {
            SecondMergeInput::Finalized(second) => {
                if self.offer.inputs.len() != 2
                    || !self.offer.transient.is_empty()
                    || second.nullifier == self.first.nullifier
                {
                    return Err(HostFailure);
                }
                Some(second)
            }
            SecondMergeInput::Staged { coin, .. } => {
                let transient = self.offer.transient.get(0).ok_or(HostFailure)?;
                let commitment = coin.commitment(&Recipient::Contract(self.address));
                let nullifier = coin.nullifier(&SenderEvidence::Contract(self.address));
                if self.offer.inputs.len() != 1
                    || self.offer.transient.len() != 1
                    || transient.coin_com != commitment
                    || transient.nullifier != nullifier
                    || transient.contract_address.as_deref() != Some(&self.address)
                    || transient.ciphertext.is_some()
                    || nullifier == self.first.nullifier
                    || zswap.nullifiers.contains_key(&nullifier)
                    || zswap.coin_coms_set.contains_key(&commitment)
                {
                    return Err(HostFailure);
                }
                None
            }
        };

        for expected in std::iter::once(&self.first).chain(second) {
            // The ledger normalizes offer order independently of the contract's inputs.
            if !self.offer.inputs.iter_deref().any(|input| {
                input.nullifier == expected.nullifier
                    && input.merkle_tree_root == expected.root
                    && input.contract_address.as_deref() == Some(&self.address)
            }) {
                return Err(HostFailure);
            }
            let info = Info::from(&expected.coin);
            let commitment = info.commitment(&Recipient::Contract(self.address));
            let nullifier = info.nullifier(&SenderEvidence::Contract(self.address));
            let capacity = 1u64.checked_shl(u32::from(zswap.coin_coms.height()));
            let leaf = capacity
                .filter(|capacity| expected.coin.mt_index < *capacity)
                .and_then(|_| zswap.coin_coms.index(expected.coin.mt_index));
            let Some((leaf_hash, owner)) = leaf else {
                return Err(HostFailure);
            };
            if commitment != expected.commitment
                || nullifier != expected.nullifier
                || zswap.nullifiers.contains_key(&nullifier)
                || !zswap.coin_coms_set.contains_key(&commitment)
                || !zswap.past_roots.contains(&expected.root)
                || expected.root != current_root
                || leaf_hash != commitment.0
                || owner.as_deref() != Some(&self.address)
                || expected.coin.mt_index >= zswap.first_free
            {
                return Err(HostFailure);
            }
            let current_coin = map_coin_by_nonce(&contract, expected.coin.nonce)
                .map_err(|_| HostFailure)?;
            if current_coin != expected.coin {
                return Err(HostFailure);
            }
        }

        Ok(())
    }
}

impl DevelopmentFunding<'_> {
    /// Merge two live contract-owned Map coins into one guaranteed contract-owned output.
    pub async fn bind_shielded_map_merge(
        self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        rng: StdRng,
    ) -> Result<BoundTransaction> {
        self.bind_shielded_merge(target, current, inputs, None, parameters, cache, signer, rng)
            .await
    }

    /// Merge a finalized Map coin with a coin minted and consumed in the same operation.
    pub async fn bind_minted_shielded_map_merge(
        self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        mint_amount: u64,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        rng: StdRng,
    ) -> Result<BoundTransaction> {
        self.bind_shielded_merge(
            target, current, inputs, Some(mint_amount), parameters, cache, signer, rng,
        )
        .await
    }

    async fn bind_shielded_merge(
        mut self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        mint_amount: Option<u64>,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        mut rng: StdRng,
    ) -> Result<BoundTransaction> {
        let policy = self.node.policy.clone();
        check(policy.genesis == DEVELOPMENT_GENESIS, Error::Policy)?;
        check(inputs.len() == if mint_amount.is_some() { 4 } else { 2 }, Error::State)?;
        let nonce_a = Nonce(read_bytes32(&inputs, "nonceA")?);
        let nonce_b = Nonce(read_bytes32(&inputs, "nonceB")?);
        check(nonce_a != nonce_b, Error::State)?;
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
        let current_contract = snapshot.state.contract.get(&address).ok_or(Error::State)?;
        let current_state = tagged_state_bytes(&current_contract)?;
        let coin_a = map_coin_by_nonce(&current_contract, nonce_a)?;
        let info_a = Info::from(&coin_a);
        let (info_b, finalized, domain) = if let Some(amount) = mint_amount {
            let domain = read_bytes32(&inputs, "domain")?;
            let type_ = address.custom_shielded_token_type(domain);
            check(amount > 0 && type_.0 == read_bytes32(&inputs, "colorB")?, Error::State)?;
            (
                Info { nonce: nonce_b, type_, value: u128::from(amount) },
                None,
                Some(domain),
            )
        } else {
            let coin = map_coin_by_nonce(&current_contract, nonce_b)?;
            (Info::from(&coin), Some(coin), None)
        };
        check(coin_a.nonce == nonce_a && info_b.nonce == nonce_b, Error::State)?;
        check(info_a.type_ == info_b.type_, Error::State)?;
        let amount = info_a.value.checked_add(info_b.value).ok_or(Error::State)?;
        let output_info = info_a.evolve_from(b"midnight:kernel:nonce_evolve", amount, info_a.type_);
        let zswap = &snapshot.state.zswap;

        let StagedContractInput {
            input: input_a,
            commitment: input_commitment_a,
            nullifier: input_nullifier_a,
            merkle_tree_root: input_root_a,
        } = stage_contract_owned_input(zswap, address, &coin_a, &mut rng)?;
        let StagedContractOutput {
            output,
            commitment: output_commitment,
        } = stage_contract_owned_output(address, &output_info, &mut rng)?;
        let (offer, second) = if let Some(coin) = finalized {
            let staged = stage_contract_owned_input(zswap, address, &coin, &mut rng)?;
            check(input_nullifier_a != staged.nullifier, Error::State)?;
            let offer = Offer::new(vec![input_a, staged.input], vec![output], vec![])
                .ok_or(Error::State)?;
            let second = BookedMergeInput {
                coin,
                commitment: staged.commitment,
                nullifier: staged.nullifier,
                root: staged.merkle_tree_root,
            };
            (offer, SecondMergeInput::Finalized(second))
        } else {
            let domain = domain.ok_or(Error::State)?;
            let transient = stage_contract_owned_transient(address, &info_b, &mut rng)?;
            check(
                input_nullifier_a != transient.nullifier && transient.coin_com != output_commitment,
                Error::State,
            )?;
            let offer = Offer::new(vec![input_a], vec![output], vec![transient])
                .ok_or(Error::State)?;
            (offer, SecondMergeInput::Staged { coin: info_b, domain })
        };
        let (_, indices) = zswap.try_apply(&offer, None).map_err(|_| Error::State)?;
        check(indices.contains_key(&output_commitment), Error::State)?;
        if let SecondMergeInput::Staged { coin, .. } = &second {
            let transient = coin.commitment(&Recipient::Contract(address));
            check(indices.size() == 2 && indices.contains_key(&transient), Error::State)?;
        }
        let booked_indices = indices.clone();

        let prepared = PreparedProof::from_contract_witness_inputs_with_com_indices(
            target,
            current,
            inputs,
            indices,
            &mut rng,
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
        check(
            binding.current_state_bytes() == Some(current_state.as_slice()),
            Error::State,
        )?;

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

        self.shielded_merge = Some(BookedMerge {
            offer,
            randomness,
            address,
            current_state,
            first: BookedMergeInput {
                coin: coin_a,
                commitment: input_commitment_a,
                nullifier: input_nullifier_a,
                root: input_root_a,
            },
            second,
            output: output_commitment,
            indices: booked_indices,
        });
        let booked = self.shielded_merge.as_ref().ok_or(Error::State)?;
        let bound = BoundTransaction::prepare_shielded_merge(
            proved.native(),
            &booked.offer,
            booked.staged_mint(),
            policy,
            self.node,
            &self,
            signer,
        )
        .await
        .map_err(|_| Error::State)?;
        check(bound.expected_state() == binding.expected_state(), Error::State)?;
        Ok(bound)
    }
}

#[cfg(all(test, feature = "zkir-321"))]
mod tests {
    use super::*;
    use crate::{
        artifacts::{self, ContractBundleSet, Role},
        client::{BoundTransaction, ChainAdapter, FinalizedReceipt, NetworkPolicy, Submission},
        funding::{CONTRACT_SEGMENT, FeePolicy, UnsealedTransaction},
        localnet::{ExplicitSeal, Node},
        proof::WitnessContractTarget,
        zkir::IrSource,
    };
    use anyhow::{Context, Result, ensure};
    use base_crypto::{fab::AlignedValue, hash::HashOutput};
    use coin_structure::{
        coin::Info,
        contract::ContractAddress,
        transfer::{Recipient, SenderEvidence},
    };
    use onchain_runtime::state::StateValue;
    use rand::{rngs::OsRng, SeedableRng};
    use serde_json::{json, Value as Json};
    use transient_crypto::proofs::Zkir;
    use std::{
        collections::BTreeMap,
        env,
        path::Path,
        thread,
        time::{Duration, Instant},
    };

    #[test]
    fn staged_merge_claims_reject_wrong_mint_and_transient_shape() {
        use crate::client::shielded_merge_claims_match;
        use base_crypto::time::{Duration as LedgerDuration, Timestamp};
        use onchain_runtime::context::Effects;

        let mut rng = StdRng::from_seed([0x5a; 32]);
        let address = ContractAddress(HashOutput([0x21; 32]));
        let domain = HashOutput([0x31; 32]);
        let type_ = address.custom_shielded_token_type(domain);
        let a = Info::new(&mut rng, 5, type_);
        let b = Info::new(&mut rng, 7, type_);
        let c = a.evolve_from(b"midnight:kernel:nonce_evolve", 12, type_);
        let seed = stage_contract_owned_output(address, &a, &mut rng).unwrap();
        let zswap = zswap::ledger::State::<Db>::new();
        let offer = Offer::new(vec![], vec![seed.output], vec![]).unwrap();
        let (zswap, indices) = zswap.try_apply(&offer, None).unwrap();
        let zswap = zswap.post_block_update(Timestamp::from_secs(1), LedgerDuration::from_secs(3600));
        let a = a.qualify(*indices.get(&seed.commitment).unwrap());
        let input = stage_contract_owned_input(&zswap, address, &a, &mut rng).unwrap();
        let output = stage_contract_owned_output(address, &c, &mut rng).unwrap();
        let transient = stage_contract_owned_transient(address, &b, &mut rng).unwrap();
        let effects = Effects {
            claimed_nullifiers: [input.nullifier, transient.nullifier].into_iter().collect(),
            claimed_shielded_receives: [output.commitment, transient.coin_com].into_iter().collect(),
            claimed_shielded_spends: [output.commitment].into_iter().collect(),
            shielded_mints: [(domain, 7)].into_iter().collect(),
            ..Effects::default()
        };
        let offer = Offer::new(vec![input.input], vec![output.output], vec![transient.clone()]).unwrap();
        assert!(shielded_merge_claims_match(&effects, address, &offer, Some((&b, domain))));
        let wrong_amount = Info { value: 8, ..b.clone() };
        assert!(!shielded_merge_claims_match(&effects, address, &offer, Some((&wrong_amount, domain))));
        assert!(!shielded_merge_claims_match(
            &effects, address, &offer, Some((&b, HashOutput([0x32; 32]))),
        ));
        let mut duplicate = offer.clone();
        duplicate.transient = [transient.clone(), transient].into_iter().collect();
        assert!(!shielded_merge_claims_match(&effects, address, &duplicate, Some((&b, domain))));
    }

    async fn finalize(node: &Node, bound: &BoundTransaction) -> Result<FinalizedReceipt> {
        let sent = node
            .submit(bound)
            .await
            .map_err(|_| anyhow::anyhow!("submit failed"))?;
        ensure!(sent != Submission::Rejected, "node rejected transaction");
        let deadline = Instant::now() + Duration::from_secs(90);
        loop {
            if let Some(receipt) = node.finalized_receipt(bound)? {
                bound.check_receipt(&receipt)?;
                return Ok(receipt);
            }
            ensure!(Instant::now() < deadline, "finalized receipt did not arrive");
            thread::sleep(Duration::from_millis(500));
        }
    }

    fn bytes_input(value: &[u8; 32]) -> Json {
        json!({"kind":"bytes", "values":value})
    }

    fn mint_inputs(coin: &Info, domain: HashOutput) -> BTreeMap<String, Json> {
        BTreeMap::from([
            ("domain".into(), bytes_input(&domain.0)),
            ("nonce".into(), bytes_input(&coin.nonce.0.0)),
            ("color".into(), bytes_input(&coin.type_.0.0)),
            ("amount".into(), json!(coin.value.to_string())),
        ])
    }

    fn merge_inputs(coin_a: &Info, coin_b: &Info) -> BTreeMap<String, Json> {
        BTreeMap::from([
            ("nonceA".into(), bytes_input(&coin_a.nonce.0.0)),
            ("nonceB".into(), bytes_input(&coin_b.nonce.0.0)),
        ])
    }

    fn parameters_from_env(setting: &impl Fn(&str) -> Result<String>, name: &str) -> Result<ProofCache> {
        ProofCache::new(
            setting(name)?.into(),
            "https://srs.midnight.network/".parse()?,
        )
        .map_err(Into::into)
    }

    #[test]
    #[ignore = "requires generated mint/merge bundles and the isolated funded development node"]
    fn funded_shielded_map_merge_localnet() -> Result<()> {
        funded_merge(false)
    }

    #[test]
    #[ignore = "requires same-operation mint/merge bundles and the isolated funded development node"]
    fn funded_shielded_map_immediate_merge_localnet() -> Result<()> {
        funded_merge(true)
    }

    fn funded_merge(immediate: bool) -> Result<()> {
        futures::executor::block_on(async {
            let setting = |name: &str| env::var(name).with_context(|| format!("missing {name}"));
            let mint_bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_MERGE_MINT_BUNDLE")?),
                Some(&setting("NOCTIUM_MERGE_MINT_MANIFEST_SHA256")?),
            )?;
            let merge_bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_MERGE_BUNDLE")?),
                Some(&setting("NOCTIUM_MERGE_MANIFEST_SHA256")?),
            )?;
            let mint_circuit = IrSource::load(mint_bundle.file(Role::Circuit)?)?;
            let merge_circuit = IrSource::load(merge_bundle.file(Role::Circuit)?)?;
            let cache = parameters_from_env(&setting, "NOCTIUM_MERGE_PARAMETER_CACHE")?;
            let policy = NetworkPolicy {
                network_id: "undeployed".into(),
                genesis: DEVELOPMENT_GENESIS.into(),
                spec_version: 2_001_100,
                transaction_version: 4,
                profile: crate::profile::NAME.into(),
                max_dust: 10u128.pow(22),
            };
            let node = Node::connect(
                &setting("NOCTIUM_MERGE_NODE")?,
                policy.clone(),
                Duration::from_secs(15),
                64 * 1024 * 1024,
                100_000,
            )?;
            let mut dust_seed = [0; 32];
            dust_seed[31] = 1;
            node.attach_dust_seed(&dust_seed)?;
            let dust = cache.dust().await?;
            let dust_parameters = cache.parameters(dust.k()).await?;
            let mint_parameters = cache.parameters(mint_circuit.k()).await?;
            let merge_parameters = cache.parameters(merge_circuit.k()).await?;
            let ttl = node.sync()?.block.tblock.to_secs() + 1800;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![mint_bundle, merge_bundle])?,
                br#"{"state":{"pot":[]}}"#,
                ttl,
                &mut OsRng,
            )?;
            let mint = target.operation("mint", &mint_parameters, ttl)?;
            let merge = target.operation("merge", &merge_parameters, ttl)?;
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
                let approve = |_: &UnsealedTransaction, candidate: &NetworkPolicy| {
                    *candidate == policy
                };
                ExplicitSeal::new(approve, StdRng::from_entropy())
            };
            let (_, deployment_intent) = target
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
                .map_err(|error| anyhow::anyhow!("deployment proof: {error:?}"))?;
            let deploy = BoundTransaction::prepare(
                &deployment_intent,
                policy.clone(),
                &node,
                &make_funding(),
                &make_signer(),
            )
            .await
            .context("prepare merge contract deployment")?;
            let deployed = finalize(&node, &deploy)
                .await
                .context("finalize merge contract deployment")?;
            let mut current = target
                .deployment_binding("mint")?
                .admit_committed_state(
                    &deployed.contract_state,
                    deploy.expected_state(),
                    &deployed.finalized_hash,
                    true,
                )
                .context("admit deployed state")?;
            let address_bytes: [u8; 32] = hex::decode(target.contract_address())?
                .try_into()
                .map_err(|_| anyhow::anyhow!("wrong contract address size"))?;
            let address = ContractAddress(HashOutput(address_bytes));
            let domain = HashOutput([3; 32]);
            let mut coin_rng = StdRng::from_entropy();
            let coin_a = Info::new(
                &mut coin_rng,
                5,
                address.custom_shielded_token_type(domain),
            );
            let coin_b = Info::new(
                &mut coin_rng,
                7,
                address.custom_shielded_token_type(domain),
            );
            ensure!(coin_a.nonce != coin_b.nonce, "mint fixture nonces collided");

            let index_a = node.sync()?.state.zswap.first_free;
            let (deposit_a, binding_a) = make_funding()
                .bind_minted_shielded_receive_with_binding(
                    &mint,
                    &current,
                    mint_inputs(&coin_a, domain),
                    &coin_a,
                    &mint_parameters,
                    &cache,
                    &make_signer(),
                    StdRng::from_entropy(),
                )
                .await
                .context("bind first merge input mint")?;
            let receipt_a = finalize(&node, &deposit_a)
                .await
                .context("finalize first merge input mint")?;
            current = binding_a
                .admit_committed_state(
                    &receipt_a.contract_state,
                    deposit_a.expected_state(),
                    &receipt_a.finalized_hash,
                    false,
                )
                .context("admit first merge input state")?;
            let state_a: ContractState<Db> = super::super::native_decode(&receipt_a.contract_state)?;
            let qualified_a = map_coin_by_nonce(&state_a, coin_a.nonce)?;
            ensure!(
                qualified_a.value == coin_a.value && qualified_a.mt_index == index_a,
                "first minted Map coin differs from its finalized booking"
            );

            let (mint_b_height, state_before_merge) = if immediate {
                (None, state_a)
            } else {
                let index_b = node.sync()?.state.zswap.first_free;
                let (deposit_b, binding_b) = make_funding()
                    .bind_minted_shielded_receive_with_binding(
                        &mint,
                        &current,
                        mint_inputs(&coin_b, domain),
                        &coin_b,
                        &mint_parameters,
                        &cache,
                        &make_signer(),
                        StdRng::from_entropy(),
                    )
                    .await
                    .context("bind second merge input mint")?;
                let receipt_b = finalize(&node, &deposit_b)
                    .await
                    .context("finalize second merge input mint")?;
                current = binding_b
                    .admit_committed_state(
                        &receipt_b.contract_state,
                        deposit_b.expected_state(),
                        &receipt_b.finalized_hash,
                        false,
                    )
                    .context("admit second merge input state")?;
                let state_b: ContractState<Db> = super::super::native_decode(&receipt_b.contract_state)?;
                let qualified_b = map_coin_by_nonce(&state_b, coin_b.nonce)?;
                ensure!(
                    qualified_b.value == coin_b.value && qualified_b.mt_index == index_b,
                    "second minted Map coin differs from its finalized booking"
                );
                (Some(receipt_b.height), state_b)
            };
            let StateValue::Array(slots) = state_before_merge.data.get_ref() else {
                anyhow::bail!("expected contract state array after input mints")
            };
            let Some(StateValue::Map(coins)) = slots.get(0) else {
                anyhow::bail!("expected root shielded coin Map")
            };
            ensure!(coins.size() == if immediate { 1 } else { 2 }, "unexpected booked merge inputs");

            let merge_index = node.sync()?.state.zswap.first_free;
            let merged = coin_a.evolve_from(
                b"midnight:kernel:nonce_evolve",
                coin_a.value.checked_add(coin_b.value).context("merge amount overflow")?,
                coin_a.type_,
            );
            let output_commitment = merged.commitment(&Recipient::Contract(address));
            let merge_bound = if immediate {
                let mut inputs = merge_inputs(&coin_a, &coin_b);
                inputs.insert("domain".into(), bytes_input(&domain.0));
                inputs.insert("colorB".into(), bytes_input(&coin_b.type_.0.0));
                make_funding()
                    .bind_minted_shielded_map_merge(
                        &merge,
                        &current,
                        inputs,
                        7,
                        &merge_parameters,
                        &cache,
                        &make_signer(),
                        StdRng::from_entropy(),
                    )
                    .await
            } else {
                make_funding()
                    .bind_shielded_map_merge(
                        &merge,
                        &current,
                        merge_inputs(&coin_a, &coin_b),
                        &merge_parameters,
                        &cache,
                        &make_signer(),
                        StdRng::from_entropy(),
                    )
                    .await
            }.context("prepare shielded Map merge")?;
            let merge_receipt = finalize(&node, &merge_bound)
                .await
                .context("finalize shielded Map merge")?;
            ensure!(
                merge_receipt.contract_state == merge_bound.expected_state(),
                "finalized merge state differs from the prepared state"
            );
            let finalized_contract = node.finalized_contract_state(target.contract_address())?;
            ensure!(
                finalized_contract.bytes == merge_receipt.contract_state,
                "finalized contract query differs from the merge receipt"
            );
            let final_state: ContractState<Db> =
                super::super::native_decode(&finalized_contract.bytes)?;
            let qualified_output = map_coin_by_nonce(&final_state, merged.nonce)?;
            ensure!(
                qualified_output.value == 12
                    && qualified_output.type_ == merged.type_
                    && qualified_output.mt_index == merge_index,
                "merged Map coin differs from its finalized output booking"
            );
            let StateValue::Array(final_slots) = final_state.data.get_ref() else {
                anyhow::bail!("expected finalized contract state array")
            };
            let Some(StateValue::Map(final_coins)) = final_slots.get(0) else {
                anyhow::bail!("expected finalized root shielded coin Map")
            };
            ensure!(
                final_coins.size() == 1
                    && !final_coins.contains_key(&AlignedValue::from(coin_a.nonce))
                    && !final_coins.contains_key(&AlignedValue::from(coin_b.nonce)),
                "merge did not replace both Map inputs with one output"
            );
            let finalized = node.sync()?;
            let (leaf, owner) = finalized
                .state
                .zswap
                .coin_coms
                .index(merge_index)
                .context("finalized merged coin leaf missing")?;
            ensure!(
                leaf == output_commitment.0 && owner.as_deref() == Some(&address),
                "finalized Zswap leaf differs from the booked merged output"
            );
            for coin in [&coin_a, &coin_b] {
                ensure!(
                    finalized
                        .state
                        .zswap
                        .nullifiers
                        .contains_key(&coin.nullifier(&SenderEvidence::Contract(address))),
                    "one merge input nullifier was not finalized"
                );
            }
            if immediate {
                let transient_commitment = coin_b.commitment(&Recipient::Contract(address));
                let transient_index = merge_index.checked_add(1).context("transient index overflow")?;
                let (leaf, owner) = finalized
                    .state
                    .zswap
                    .coin_coms
                    .index(transient_index)
                    .context("same-offer transient leaf missing")?;
                ensure!(
                    leaf == transient_commitment.0 && owner.as_deref() == Some(&address),
                    "transient commitment and owner differ from the booked coin"
                );
            }
            println!(
                "{}",
                json!({
                    "deploymentHeight": deployed.height,
                    "mintAHeight": receipt_a.height,
                    "mintBHeight": mint_b_height,
                    "sameOperation": immediate,
                    "mergeHeight": merge_receipt.height,
                    "mergeTransaction": merge_receipt.transaction_id,
                    "contractAddress": target.contract_address(),
                    "inputValues": [coin_a.value, coin_b.value],
                    "outputValue": qualified_output.value,
                    "outputIndex": qualified_output.mt_index,
                    "outputCommitment": hex::encode(output_commitment.0.0),
                    "inputNullifiersSpent": true,
                    "mapReplacedTwoInputsWithOneOutput": true,
                    "mintManifestSha256": setting("NOCTIUM_MERGE_MINT_MANIFEST_SHA256")?,
                    "mergeManifestSha256": setting("NOCTIUM_MERGE_MANIFEST_SHA256")?,
                    "mintCircuitK": mint_circuit.k(),
                    "mergeCircuitK": merge_circuit.k(),
                })
            );
            Ok(())
        })
    }
}

fn read_bytes32(inputs: &BTreeMap<String, Value>, name: &str) -> Result<HashOutput> {
    let object = inputs.get(name).and_then(Value::as_object).ok_or(Error::State)?;
    check(
        object.len() == 2 && object.get("kind").and_then(Value::as_str) == Some("bytes"),
        Error::State,
    )?;
    let values = object
        .get("values")
        .and_then(Value::as_array)
        .ok_or(Error::State)?;
    check(values.len() == 32, Error::State)?;
    let mut bytes = [0u8; 32];
    for (output, value) in bytes.iter_mut().zip(values) {
        *output = u8::try_from(value.as_u64().ok_or(Error::State)?).map_err(|_| Error::State)?;
    }
    Ok(HashOutput(bytes))
}

fn tagged_state_bytes(state: &ContractState<Db>) -> Result<Vec<u8>> {
    let mut bytes = Vec::new();
    serialize::tagged_serialize(state, &mut bytes).map_err(|_| Error::State)?;
    Ok(bytes)
}

fn map_coin_by_nonce(state: &ContractState<Db>, nonce: Nonce) -> Result<QualifiedInfo> {
    let StateValue::Array(slots) = state.data.get_ref() else {
        return Err(Error::State);
    };
    let Some(StateValue::Map(coins)) = slots.get(0) else {
        return Err(Error::State);
    };
    let value = coins.get(&AlignedValue::from(nonce)).ok_or(Error::State)?;
    let StateValue::Cell(cell) = &*value else {
        return Err(Error::State);
    };
    let aligned = &**cell;
    let qualified = QualifiedInfo::try_from(&*aligned.value).map_err(|_| Error::State)?;
    check(
        qualified.nonce == nonce && *aligned == AlignedValue::from(qualified),
        Error::State,
    )?;
    Ok(qualified)
}
