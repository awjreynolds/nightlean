use super::{DEVELOPMENT_GENESIS, DevelopmentFunding, Error, ProofCache, Result, check};
use crate::{
    Db,
    client::{BoundTransaction, HostFailure, SigningAdapter, Snapshot},
    proof::{
        ContractOperationTarget, CurrentStateContext, LocalProver, PreparedProof, TrustedParameters,
    },
};
use base_crypto::{fab::AlignedValue, hash::HashOutput, rng::SplittableRng};
use coin_structure::{
    coin::{Commitment, Info, Nonce, Nullifier, PublicKey, QualifiedInfo},
    contract::ContractAddress,
    transfer::{Recipient, SenderEvidence},
};
use ledger::structure::GUARANTEED_SEGMENT;
use onchain_runtime::state::{ContractState, StateValue};
use rand::rngs::StdRng;
use serde_json::Value;
use std::{collections::BTreeMap, future::pending};
use transient_crypto::{commitment::PedersenRandomness, encryption, proofs::Proof};
use zswap::{Input, Offer, Output, prove::ZswapResolver};

pub(super) struct BookedTransfer {
    pub(super) offer: Offer<Proof, Db>,
    pub(super) randomness: PedersenRandomness,
    address: ContractAddress,
    current_state: Vec<u8>,
    qualified_coin: QualifiedInfo,
    input_commitment: Commitment,
    input_nullifier: Nullifier,
    input_root: transient_crypto::merkle_tree::MerkleTreeDigest,
    output_commitment: Commitment,
    output_index: u64,
}

impl BookedTransfer {
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
        let mut bytes = Vec::new();
        serialize::tagged_serialize(&*current_state, &mut bytes).map_err(|_| HostFailure)?;
        let zswap = &snapshot.state.zswap;
        let info = Info::from(&self.qualified_coin);
        let commitment = info.commitment(&Recipient::Contract(self.address));
        let nullifier = info.nullifier(&SenderEvidence::Contract(self.address));
        let capacity = 1u64.checked_shl(u32::from(zswap.coin_coms.height()));
        let leaf = capacity
            .filter(|capacity| self.qualified_coin.mt_index < *capacity)
            .and_then(|_| zswap.coin_coms.index(self.qualified_coin.mt_index));
        let Some((leaf_hash, owner)) = leaf else {
            return Err(HostFailure);
        };

        if bytes != self.current_state
            || !zswap.coin_coms_set.contains_key(&commitment)
            || commitment != self.input_commitment
            || nullifier != self.input_nullifier
            || zswap.nullifiers.contains_key(&nullifier)
            || !zswap.past_roots.contains(&self.input_root)
            || leaf_hash != commitment.0
            || owner.as_deref() != Some(&self.address)
            || self.qualified_coin.mt_index >= zswap.first_free
            || indices.get(&self.output_commitment).as_deref() != Some(&self.output_index)
            || self.offer.inputs.len() != 1
            || self.offer.outputs.len() != 1
            || !self.offer.transient.is_empty()
            || self.offer.inputs.get(0).is_none_or(|input| {
                input.nullifier != self.input_nullifier
                    || input.merkle_tree_root != self.input_root
                    || input.contract_address.as_deref() != Some(&self.address)
            })
            || self.offer.outputs.get(0).is_none_or(|output| {
                output.coin_com != self.output_commitment
                    || output.contract_address.is_some()
                    || output.ciphertext.is_none()
            })
        {
            return Err(HostFailure);
        }
        Ok(())
    }
}

impl DevelopmentFunding<'_> {
    /// Bind a single contract-owned Map coin to one encrypted user output.
    pub async fn bind_shielded_map_spend(
        mut self,
        target: &ContractOperationTarget,
        current: &CurrentStateContext,
        inputs: BTreeMap<String, Value>,
        recipient_encryption_key: encryption::PublicKey,
        parameters: &TrustedParameters,
        cache: &ProofCache,
        signer: &impl SigningAdapter,
        mut rng: StdRng,
    ) -> Result<BoundTransaction> {
        let policy = self.node.policy.clone();
        check(policy.genesis == DEVELOPMENT_GENESIS, Error::Policy)?;
        check(inputs.len() == 2, Error::State)?;
        let nonce = Nonce(read_bytes32(&inputs, "nonce")?);
        let recipient = PublicKey(read_bytes32(&inputs, "recipient")?);
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
        let qualified_coin = map_coin_by_nonce(&current_contract, nonce)?;
        check(qualified_coin.nonce == nonce, Error::State)?;

        let info = Info::from(&qualified_coin);
        let commitment = info.commitment(&Recipient::Contract(address));
        let nullifier = info.nullifier(&SenderEvidence::Contract(address));
        let zswap = &snapshot.state.zswap;
        let capacity = 1u64
            .checked_shl(u32::from(zswap.coin_coms.height()))
            .ok_or(Error::State)?;
        check(
            qualified_coin.mt_index < capacity
                && qualified_coin.mt_index < zswap.first_free
                && zswap.coin_coms_set.contains_key(&commitment)
                && !zswap.nullifiers.contains_key(&nullifier)
                && zswap
                    .past_roots
                    .contains(&zswap.coin_coms.root().ok_or(Error::State)?),
            Error::State,
        )?;
        let (leaf_hash, owner) = zswap
            .coin_coms
            .index(qualified_coin.mt_index)
            .ok_or(Error::State)?;
        check(
            leaf_hash == commitment.0 && owner.as_deref() == Some(&address),
            Error::State,
        )?;

        let prepared =
            PreparedProof::from_contract_witness_inputs(target, current, inputs, &mut rng)
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

        let input = Input::<_, Db>::new_contract_owned(
            &mut rng,
            &qualified_coin,
            Some(GUARANTEED_SEGMENT),
            address,
            &zswap.coin_coms,
        )
        .map_err(|_| Error::State)?;
        let output_info = info.evolve_from(
            b"midnight:kernel:nonce_evolve",
            qualified_coin.value,
            qualified_coin.type_,
        );
        let output = Output::<_, Db>::new(
            &mut rng,
            &output_info,
            Some(GUARANTEED_SEGMENT),
            &recipient,
            Some(recipient_encryption_key),
        )
        .map_err(|_| Error::State)?;
        let input_root = input.merkle_tree_root;
        let output_commitment = output.coin_com;
        let offer = Offer::new(vec![input], vec![output], vec![]).ok_or(Error::State)?;
        let (_, indices) = zswap.try_apply(&offer, None).map_err(|_| Error::State)?;
        let output_index = *indices.get(&output_commitment).ok_or(Error::State)?;

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

        self.shielded_transfer = Some(BookedTransfer {
            offer,
            randomness,
            address,
            current_state,
            qualified_coin,
            input_commitment: commitment,
            input_nullifier: nullifier,
            input_root,
            output_commitment,
            output_index,
        });
        let expected = &self.shielded_transfer.as_ref().ok_or(Error::State)?.offer;
        let bound = BoundTransaction::prepare_shielded_transfer(
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
}

fn read_bytes32(inputs: &BTreeMap<String, Value>, name: &str) -> Result<HashOutput> {
    let value = inputs.get(name).ok_or(Error::State)?;
    let object = value.as_object().ok_or(Error::State)?;
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
    use coin_structure::transfer::Recipient as CoinRecipient;
    use ledger::structure::Transaction;
    use rand::{SeedableRng, rngs::OsRng};
    use serde_json::json;
    use std::{
        env,
        path::Path,
        thread,
        time::{Duration, Instant},
    };
    use transient_crypto::proofs::Zkir;
    use zswap::keys::SecretKeys;

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

    fn nonce_input(nonce: Nonce) -> Value {
        json!({"kind":"bytes", "values":nonce.0.0})
    }

    fn spend_inputs(nonce: Nonce, recipient: PublicKey) -> BTreeMap<String, Value> {
        BTreeMap::from([
            ("nonce".into(), nonce_input(nonce)),
            (
                "recipient".into(),
                json!({"kind":"bytes", "values":recipient.0.0}),
            ),
        ])
    }

    fn map_contains(state: &ContractState<Db>, nonce: Nonce) -> Result<bool> {
        let StateValue::Array(slots) = state.data.get_ref() else {
            anyhow::bail!("expected state array");
        };
        let Some(StateValue::Map(coins)) = slots.get(0) else {
            anyhow::bail!("expected qualified coin Map in slot 0");
        };
        Ok(coins.contains_key(&AlignedValue::from(nonce)))
    }

    #[test]
    #[ignore = "requires generated tip/spend bundles and isolated development node"]
    fn funded_shielded_map_spend_localnet() -> Result<()> {
        futures::executor::block_on(async {
            let setting = |name| env::var(name).with_context(|| format!("missing {name}"));
            let tip_bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_TRANSFER_TIP_BUNDLE")?),
                Some(&setting("NOCTIUM_TRANSFER_TIP_MANIFEST_SHA256")?),
            )?;
            let spend_bundle = artifacts::verify(
                Path::new(&setting("NOCTIUM_TRANSFER_SPEND_BUNDLE")?),
                Some(&setting("NOCTIUM_TRANSFER_SPEND_MANIFEST_SHA256")?),
            )?;
            let tip_circuit = IrSource::load(tip_bundle.file(Role::Circuit)?)?;
            let spend_circuit = IrSource::load(spend_bundle.file(Role::Circuit)?)?;
            let cache = ProofCache::new(
                setting("NOCTIUM_TRANSFER_PARAMETER_CACHE")?.into(),
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
                &setting("NOCTIUM_TRANSFER_NODE")?,
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
            let tip_parameters = cache.parameters(tip_circuit.k()).await?;
            let spend_parameters = cache.parameters(spend_circuit.k()).await?;
            let ttl = node.sync()?.block.tblock.to_secs() + 1800;
            let target = WitnessContractTarget::from_state_config(
                ContractBundleSet::new(vec![tip_bundle, spend_bundle])?,
                br#"{"state":{"pot":[]}}"#,
                ttl,
                &mut OsRng,
            )?;
            let tip = target.operation("tip", &tip_parameters, ttl)?;
            let spend = target.operation("spend", &spend_parameters, ttl)?;
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
            let deploy_signer = make_signer();
            let (_, deploy_intent) = target
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
                &deploy_intent,
                policy.clone(),
                &node,
                &make_funding(),
                &deploy_signer,
            )
            .await
            .context("prepare deployment")?;
            let deployed = finalize(&node, &deploy)
                .await
                .context("finalize deployment")?;
            let mut current = target
                .deployment_binding("tip")?
                .admit_committed_state(
                    &deployed.contract_state,
                    deploy.expected_state(),
                    &deployed.finalized_hash,
                    true,
                )
                .context("restore post-deployment state")?;

            let address = ContractAddress(HashOutput(
                hex::decode(target.contract_address())?
                    .try_into()
                    .map_err(|_| anyhow::anyhow!("wrong contract address size"))?,
            ));
            let domain = HashOutput([7; 32]);
            let mut rng = StdRng::from_entropy();
            let coin = Info::new(&mut rng, 5, address.custom_shielded_token_type(domain));
            let snapshot = node.sync()?;
            let expected_index = snapshot.state.zswap.first_free;
            let commitment = coin.commitment(&CoinRecipient::Contract(address));
            let tip_inputs = || {
                BTreeMap::from([
                    ("domain".into(), json!({"kind":"bytes", "values":domain.0})),
                    ("nonce".into(), nonce_input(coin.nonce)),
                    (
                        "color".into(),
                        json!({"kind":"bytes", "values":coin.type_.0.0}),
                    ),
                ])
            };
            let tip_signer = make_signer();
            let receive = make_funding()
                .bind_minted_shielded_receive_with_binding(
                    &tip,
                    &current,
                    tip_inputs(),
                    &coin,
                    &tip_parameters,
                    &cache,
                    &tip_signer,
                    StdRng::from_entropy(),
                )
                .await
                .context("bind tip deposit")?;
            let tip_receipt = finalize(&node, &receive.0)
                .await
                .context("finalize tip deposit")?;
            current = receive
                .1
                .admit_committed_state(
                    &tip_receipt.contract_state,
                    receive.0.expected_state(),
                    &tip_receipt.finalized_hash,
                    false,
                )
                .context("restore post-tip state")?;
            let state: ContractState<Db> = super::super::native_decode(&tip_receipt.contract_state)
                .context("decode tip receipt state")?;
            let qualified_coin =
                map_coin_by_nonce(&state, coin.nonce).context("read tip Map coin")?;
            ensure!(
                qualified_coin.mt_index == expected_index,
                "tip did not book expected index"
            );
            ensure!(
                qualified_coin.value == 5,
                "tip did not deposit the nonzero fixture amount"
            );
            ensure!(
                snapshot
                    .state
                    .zswap
                    .coin_coms_set
                    .get(&commitment)
                    .is_none(),
                "fixture commitment unexpectedly existed before tip"
            );
            let deposited_snapshot = node.sync()?;
            let finalized_contract = deposited_snapshot
                .state
                .contract
                .get(&address)
                .ok_or_else(|| anyhow::anyhow!("finalized contract missing"))?;
            ensure!(
                tagged_state_bytes(&finalized_contract)? == tip_receipt.contract_state,
                "refreshed finalized state differs from the deposit receipt"
            );
            ensure!(
                map_coin_by_nonce(&finalized_contract, coin.nonce)? == qualified_coin
                    && deposited_snapshot
                        .state
                        .zswap
                        .coin_coms_set
                        .contains_key(&commitment),
                "refreshed finalized state does not contain the qualified deposit"
            );

            let keys = SecretKeys::from_rng_seed(&mut rng);
            let recipient_coin_key = keys.coin_public_key();
            let recipient_encryption_key = keys.enc_public_key();
            let expected_output_index = node.sync()?.state.zswap.first_free;
            let mismatch_signer = make_signer();
            ensure!(
                make_funding()
                    .bind_shielded_map_spend(
                        &spend,
                        &current,
                        spend_inputs(Nonce(HashOutput([0x55; 32])), recipient_coin_key),
                        recipient_encryption_key,
                        &spend_parameters,
                        &cache,
                        &mismatch_signer,
                        StdRng::from_entropy(),
                    )
                    .await
                    .is_err(),
                "mismatched nonce bound a spend"
            );
            ensure!(
                node.finalized_contract_state(target.contract_address())?
                    .bytes
                    == tip_receipt.contract_state,
                "mismatched nonce changed the contract Map"
            );
            let spend_signer = make_signer();
            let spend_bound = make_funding()
                .bind_shielded_map_spend(
                    &spend,
                    &current,
                    spend_inputs(coin.nonce, recipient_coin_key),
                    recipient_encryption_key,
                    &spend_parameters,
                    &cache,
                    &spend_signer,
                    StdRng::from_entropy(),
                )
                .await
                .context("bind shielded Map spend")?;
            let spend_receipt = finalize(&node, &spend_bound)
                .await
                .context("finalize shielded Map spend")?;
            let spent_state: ContractState<Db> =
                super::super::native_decode(&spend_receipt.contract_state)
                    .context("decode spend receipt state")?;
            ensure!(
                !map_contains(&spent_state, coin.nonce)?,
                "spent Map entry remains"
            );

            let spent_snapshot = node.sync()?;
            let input_nullifier =
                Info::from(&qualified_coin).nullifier(&SenderEvidence::Contract(address));
            ensure!(
                spent_snapshot
                    .state
                    .zswap
                    .nullifiers
                    .contains_key(&input_nullifier),
                "spend nullifier missing from finalized Zswap state"
            );
            let output_coin = Info::from(&qualified_coin).evolve_from(
                b"midnight:kernel:nonce_evolve",
                qualified_coin.value,
                qualified_coin.type_,
            );
            let output_commitment =
                output_coin.commitment(&CoinRecipient::User(recipient_coin_key));
            let (output_leaf, output_owner) = spent_snapshot
                .state
                .zswap
                .coin_coms
                .index(expected_output_index)
                .ok_or_else(|| anyhow::anyhow!("encrypted output leaf missing"))?;
            ensure!(
                output_leaf == output_commitment.0
                    && output_owner.is_none()
                    && spent_snapshot
                        .state
                        .zswap
                        .coin_coms_set
                        .contains_key(&output_commitment),
                "finalized output commitment or owner mismatch"
            );
            ensure!(
                expected_index.checked_add(1) == Some(expected_output_index),
                "deposit did not advance the Zswap output cursor"
            );
            let sealed: crate::funding::SealedTransaction =
                serialize::tagged_deserialize(spend_bound.bytes())?;
            let Transaction::Standard(transaction) = sealed else {
                anyhow::bail!("expected a standard transaction");
            };
            let output = transaction
                .guaranteed_coins
                .as_deref()
                .ok_or_else(|| anyhow::anyhow!("missing guaranteed offer"))?;
            ensure!(output.outputs.len() == 1, "unexpected output count");
            let ciphertext = output
                .outputs
                .get(0)
                .and_then(|output| output.ciphertext.as_deref())
                .ok_or_else(|| anyhow::anyhow!("missing encrypted output"))?;
            ensure!(
                keys.try_decrypt(ciphertext) == Some(output_coin),
                "recipient could not decrypt the exact output coin"
            );

            let replay_signer = make_signer();
            ensure!(
                make_funding()
                    .bind_shielded_map_spend(
                        &spend,
                        &current,
                        spend_inputs(coin.nonce, recipient_coin_key),
                        recipient_encryption_key,
                        &spend_parameters,
                        &cache,
                        &replay_signer,
                        StdRng::from_entropy(),
                    )
                    .await
                    .is_err(),
                "replayed nonce bound another spend"
            );
            ensure!(
                node.finalized_contract_state(target.contract_address())?
                    .bytes
                    == spend_receipt.contract_state,
                "replayed nonce changed the contract Map"
            );
            println!(
                "{}",
                json!({
                    "deploymentHeight": deployed.height,
                    "tipHeight": tip_receipt.height,
                    "spendHeight": spend_receipt.height,
                    "spendTransaction": spend_receipt.transaction_id,
                    "inputNonce": hex::encode(coin.nonce.0.0),
                    "inputCommitment": hex::encode(commitment.0.0),
                    "inputNullifier": hex::encode(input_nullifier.0.0),
                    "outputCommitment": hex::encode(output_commitment.0.0),
                    "outputIndex": expected_output_index,
                    "decryptedOutput": true,
                    "rejected": ["mismatchedNonce", "replayedNonce"],
                    "contractStateSha256": artifacts::digest(&spend_receipt.contract_state)
                })
            );
            Ok(())
        })
    }
}
