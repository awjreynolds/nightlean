//! Bounded native DUST fee construction. The host owns wallet state, keys and approval.
use crate::{
    Db,
    proof::{ProvedNativeIntent, TrustedParameters},
};
use base_crypto::{rng::SplittableRng, time::Timestamp};
use coin_structure::coin::TokenType;
use ledger::{
    dust::{DUST_EXPECTED_FILES, DustActions, DustLocalState, DustOutput, DustSecretKey},
    structure::{
        Intent, LedgerParameters, ProofMarker, Signature, StandardTransaction, Transaction,
    },
};
use rand::rngs::StdRng;
use sha2::{Digest, Sha256};
use std::io;
use storage::arena::Sp;
use transient_crypto::{
    commitment::{PedersenRandomness, PureGeneratorPedersen},
    proofs::{KeyLocation, ProvingKeyMaterial, Resolver, Zkir},
};

pub type UnsealedTransaction = Transaction<Signature, ProofMarker, PedersenRandomness, Db>;
pub type SealedTransaction = Transaction<Signature, ProofMarker, PureGeneratorPedersen, Db>;
pub const CONTRACT_SEGMENT: u16 = 1;
pub const FUNDING_SEGMENT: u16 = 2;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Error {
    Material,
    Parameters,
    Wallet,
    Budget,
    Limits,
    Balance,
    Proof,
    Intent,
}
impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "nightlean_funding_{self:?}")
    }
}
impl std::error::Error for Error {}
type Result<T> = std::result::Result<T, Error>;

/// Official system-precompile material, authenticated against hashes pinned by the ledger.
/// The legacy DUST circuit is separate from the selected 3.x Lean contract circuit.
pub struct DustMaterial {
    material: ProvingKeyMaterial,
    k: u8,
}
impl DustMaterial {
    pub fn from_bytes(prover: &[u8], verifier: &[u8], circuit: &[u8]) -> Result<Self> {
        for (suffix, bytes) in [
            ("spend.prover", prover),
            ("spend.verifier", verifier),
            ("spend.bzkir", circuit),
        ] {
            let (_, expected, _) = DUST_EXPECTED_FILES
                .iter()
                .find(|(path, _, _)| path.ends_with(suffix))
                .ok_or(Error::Material)?;
            if bytes.is_empty()
                || bytes.len() > 16 * 1024 * 1024
                || Sha256::digest(bytes).as_slice() != expected
            {
                return Err(Error::Material);
            }
        }
        let ir = builtin_zkir::IrSource::load_from_tagged(io::Cursor::new(circuit))
            .map_err(|_| Error::Material)?;
        let k = ir.k();
        if !(1..=20).contains(&k) {
            return Err(Error::Material);
        }
        Ok(Self {
            material: ProvingKeyMaterial {
                prover_key: prover.to_vec(),
                verifier_key: verifier.to_vec(),
                ir_source: circuit.to_vec(),
            },
            k,
        })
    }
    pub fn k(&self) -> u8 {
        self.k
    }
}
impl Resolver for DustMaterial {
    async fn resolve_key(&self, key: KeyLocation) -> io::Result<Option<ProvingKeyMaterial>> {
        if key.0.as_ref() == "midnight/dust/spend" {
            Ok(Some(self.material.clone()))
        } else {
            Ok(None)
        }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct FeePolicy {
    pub max_dust: u128,
    pub margin_blocks: usize,
    pub max_spends: usize,
}
impl FeePolicy {
    fn validate(self) -> Result<()> {
        if self.max_dust == 0 || self.margin_blocks > 8 || !(1..=64).contains(&self.max_spends) {
            return Err(Error::Limits);
        }
        Ok(())
    }
}

/// Private wallet state supplied by an authorized host. No Debug or ambient key derivation.
pub struct DustFunding {
    secret: DustSecretKey,
    state: DustLocalState<Db>,
}
impl DustFunding {
    pub fn new(secret: DustSecretKey, state: DustLocalState<Db>) -> Self {
        Self { secret, state }
    }
    pub fn balance(&self, time: Timestamp) -> u128 {
        self.state.wallet_balance(time)
    }

    /// Speculative selection leaves the retained wallet unchanged. Replay accepted chain events
    /// before preparing another attempt. Approval and sealing belong to the host signer.
    pub async fn fund(
        &self,
        contract: &ProvedNativeIntent,
        network_id: &str,
        parameters: &LedgerParameters,
        material: &DustMaterial,
        srs: &TrustedParameters,
        now: Timestamp,
        policy: FeePolicy,
        mut rng: StdRng,
    ) -> Result<FundedTransaction> {
        policy.validate()?;
        if self.state.params != parameters.dust || now < self.state.sync_time {
            return Err(Error::Parameters);
        }
        if material.k != srs.k() {
            return Err(Error::Parameters);
        }
        if contract.actions.len() != 1
            || contract.guaranteed_unshielded_offer.is_some()
            || contract.fallible_unshielded_offer.is_some()
            || contract.dust_actions.is_some()
            || contract.ttl <= now
            || network_id.is_empty()
            || network_id.len() > 128
        {
            return Err(Error::Intent);
        }
        let base = one_intent(network_id, CONTRACT_SEGMENT, contract.clone());
        let mut needed = 0u128;
        for _ in 0..10 {
            if needed > policy.max_dust {
                return Err(Error::Budget);
            }
            let candidate = if needed == 0 {
                base.clone()
            } else {
                let mut candidates: Vec<_> = self
                    .state
                    .utxos()
                    .filter_map(|output| {
                        let generation = self.state.generation_info(&output)?;
                        let amount = DustOutput::from(output).updated_value(
                            &generation,
                            now,
                            &parameters.dust,
                        );
                        (amount > 0).then_some((amount, output))
                    })
                    .collect();
                candidates.sort_by(|(a, _), (b, _)| b.cmp(a));
                let mut remaining = needed;
                let mut local = self.state.clone();
                let mut spends = Vec::new();
                for (amount, output) in candidates {
                    if remaining == 0 {
                        break;
                    }
                    if spends.len() == policy.max_spends {
                        return Err(Error::Limits);
                    }
                    let spent = remaining.min(amount);
                    let (next, spend) = local
                        .spend(&self.secret, &output, spent, now)
                        .map_err(|_| Error::Wallet)?;
                    local = next;
                    spends.push(spend);
                    remaining -= spent;
                }
                if remaining != 0 {
                    return Err(Error::Wallet);
                }
                let mut fee = Intent::<Signature, _, _, Db>::empty(&mut rng, contract.ttl);
                fee.dust_actions = Some(Sp::new(DustActions {
                    spends: spends.into(),
                    registrations: vec![].into(),
                    ctime: now,
                }));
                let prover = builtin_zkir::LocalProvingProvider {
                    rng: rng.split(),
                    resolver: material,
                    params: srs,
                };
                let (_, fee) = fee
                    .prove(
                        FUNDING_SEGMENT,
                        prover,
                        &parameters.cost_model.runtime_cost_model,
                    )
                    .await
                    .map_err(|_| Error::Proof)?;
                base.merge(&one_intent(network_id, FUNDING_SEGMENT, fee))
                    .map_err(|_| Error::Balance)?
            };
            // Binding seals have a fixed encoded size. Estimate from a real seal, without
            // binding a durable transaction identity or changing the retained contract intent.
            let fees = candidate
                .seal(rng.split())
                .fees_with_margin(parameters, policy.margin_blocks)
                .map_err(|_| Error::Balance)?;
            if fees > policy.max_dust {
                return Err(Error::Budget);
            }
            let deltas = candidate.balance(Some(fees)).map_err(|_| Error::Balance)?;
            let mut missing = 0;
            for ((token, _), delta) in deltas {
                if token == TokenType::Dust && delta < 0 {
                    missing += delta.unsigned_abs();
                } else if delta < 0 {
                    return Err(Error::Balance);
                }
            }
            if missing == 0 {
                return Ok(FundedTransaction {
                    transaction: candidate,
                    spent_dust: needed,
                    estimated_fee: fees,
                });
            }
            needed = needed.checked_add(missing).ok_or(Error::Budget)?;
        }
        Err(Error::Balance)
    }
}

/// Still unsealed and unbound to a journal. A host signer must authorize the complete budget.
pub struct FundedTransaction {
    transaction: UnsealedTransaction,
    spent_dust: u128,
    estimated_fee: u128,
}
impl FundedTransaction {
    pub fn native(&self) -> &UnsealedTransaction {
        &self.transaction
    }
    pub fn spent_dust(&self) -> u128 {
        self.spent_dust
    }
    pub fn estimated_fee(&self) -> u128 {
        self.estimated_fee
    }
}

pub fn one_intent(
    network_id: &str,
    segment: u16,
    intent: ProvedNativeIntent,
) -> UnsealedTransaction {
    Transaction::Standard(StandardTransaction {
        network_id: network_id.to_owned(),
        binding_randomness: intent.binding_commitment,
        intents: [(segment, intent)].into_iter().collect(),
        guaranteed_coins: None,
        fallible_coins: Default::default(),
    })
}
