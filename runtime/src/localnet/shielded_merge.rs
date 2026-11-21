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
use std::{collections::BTreeMap, future::pending};
use transient_crypto::{commitment::PedersenRandomness, proofs::Proof};
use zswap::{Offer, prove::ZswapResolver};

use super::shielded_transfer::{
    stage_contract_owned_input, stage_contract_owned_output, StagedContractInput,
    StagedContractOutput,
};

struct BookedMergeInput {
    coin: QualifiedInfo,
    commitment: Commitment,
    nullifier: Nullifier,
    root: transient_crypto::merkle_tree::MerkleTreeDigest,
}

struct BookedMergeOutput {
    commitment: Commitment,
    index: u64,
}

pub(super) struct BookedMerge {
    pub(super) offer: Offer<Proof, Db>,
    pub(super) randomness: PedersenRandomness,
    address: ContractAddress,
    current_state: Vec<u8>,
    inputs: [BookedMergeInput; 2],
    output: BookedMergeOutput,
}

impl BookedMerge {
    pub(super) fn check_booking(
        &self,
        snapshot: &Snapshot,
    ) -> std::result::Result<(), HostFailure> {
        let (_, indices) = snapshot
            .state
            .zswap
            .try_apply(&self.offer, None)
            .map_err(|_| HostFailure)?;
        let current_state = snapshot
            .state
            .contract
            .get(&self.address)
            .ok_or(HostFailure)?;
        let current_state = tagged_state_bytes(&current_state).map_err(|_| HostFailure)?;
        let zswap = &snapshot.state.zswap;
        let current_root = zswap.coin_coms.root().ok_or(HostFailure)?;
        if current_state != self.current_state
            || self.offer.inputs.len() != 2
            || self.offer.outputs.len() != 1
            || !self.offer.transient.is_empty()
            || self.offer.inputs.get(0).is_none_or(|input| {
                input.nullifier != self.inputs[0].nullifier
                    || input.merkle_tree_root != self.inputs[0].root
                    || input.contract_address.as_deref() != Some(&self.address)
            })
            || self.offer.inputs.get(1).is_none_or(|input| {
                input.nullifier != self.inputs[1].nullifier
                    || input.merkle_tree_root != self.inputs[1].root
                    || input.contract_address.as_deref() != Some(&self.address)
            })
            || self.inputs[0].nullifier == self.inputs[1].nullifier
            || self.offer.outputs.iter_deref().any(|output| {
                output.coin_com != self.output.commitment
                    || output.contract_address.as_deref() != Some(&self.address)
                    || output.ciphertext.is_some()
            })
            || self.offer.outputs.iter_deref().count() != 1
            || indices.get(&self.output.commitment).as_deref() != Some(&self.output.index)
        {
            return Err(HostFailure);
        }

        for expected in &self.inputs {
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
            let current_coin = map_coin_by_nonce(
                snapshot
                    .state
                    .contract
                    .get(&self.address)
                    .ok_or(HostFailure)?,
                expected.coin.nonce,
            )
            .map_err(|_| HostFailure)?;
            if current_coin != expected.coin {
                return Err(HostFailure);
            }
        }

        let output = self.offer.outputs.iter_deref().next().ok_or(HostFailure)?;
        if output.coin_com != self.output.commitment
            || output.contract_address.as_deref() != Some(&self.address)
            || output.ciphertext.is_some()
        {
            return Err(HostFailure);
        }
        Ok(())
    }
}

impl DevelopmentFunding<'_> {
    /// Merge two live contract-owned Map coins into one guaranteed contract-owned output.
    pub async fn bind_shielded_map_merge(
        mut self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        mut rng: StdRng,
    ) -> Result<BoundTransaction> {
        let policy = self.node.policy.clone();
        check(policy.genesis == DEVELOPMENT_GENESIS, Error::Policy)?;
        check(inputs.len() == 2, Error::State)?;
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
        let coin_b = map_coin_by_nonce(&current_contract, nonce_b)?;
        check(coin_a.nonce == nonce_a && coin_b.nonce == nonce_b, Error::State)?;
        let info_a = Info::from(&coin_a);
        let info_b = Info::from(&coin_b);
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
        let StagedContractInput {
            input: input_b,
            commitment: input_commitment_b,
            nullifier: input_nullifier_b,
            merkle_tree_root: input_root_b,
        } = stage_contract_owned_input(zswap, address, &coin_b, &mut rng)?;
        check(input_nullifier_a != input_nullifier_b, Error::State)?;
        let StagedContractOutput {
            output,
            commitment: output_commitment,
        } = stage_contract_owned_output(address, &output_info, &mut rng)?;
        let offer = Offer::new(vec![input_a, input_b], vec![output], vec![]).ok_or(Error::State)?;
        let (_, indices) = zswap.try_apply(&offer, None).map_err(|_| Error::State)?;
        let output_index = *indices.get(&output_commitment).ok_or(Error::State)?;

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
            inputs: [
                BookedMergeInput {
                    coin: coin_a,
                    commitment: input_commitment_a,
                    nullifier: input_nullifier_a,
                    root: input_root_a,
                },
                BookedMergeInput {
                    coin: coin_b,
                    commitment: input_commitment_b,
                    nullifier: input_nullifier_b,
                    root: input_root_b,
                },
            ],
            output: BookedMergeOutput {
                commitment: output_commitment,
                index: output_index,
            },
        });
        let expected = &self.shielded_merge.as_ref().ok_or(Error::State)?.offer;
        let bound = BoundTransaction::prepare_shielded_merge(
            proved.native(),
            expected,
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
                10_000,
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
            let StateValue::Array(slots) = state_b.data.get_ref() else {
                anyhow::bail!("expected contract state array after input mints")
            };
            let Some(StateValue::Map(coins)) = slots.get(0) else {
                anyhow::bail!("expected root shielded coin Map")
            };
            ensure!(coins.size() == 2, "expected two booked merge inputs");

            let merge_index = node.sync()?.state.zswap.first_free;
            let merged = coin_a.evolve_from(
                b"midnight:kernel:nonce_evolve",
                coin_a.value.checked_add(coin_b.value).context("merge amount overflow")?,
                coin_a.type_,
            );
            let output_commitment = merged.commitment(&Recipient::Contract(address));
            let merge_bound = make_funding()
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
                .context("prepare two-input shielded Map merge")?;
            let merge_receipt = finalize(&node, &merge_bound)
                .await
                .context("finalize two-input shielded Map merge")?;
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
            println!(
                "{}",
                json!({
                    "deploymentHeight": deployed.height,
                    "mintAHeight": receipt_a.height,
                    "mintBHeight": receipt_b.height,
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
