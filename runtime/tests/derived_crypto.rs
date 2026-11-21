#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Expr, Plan, Value, check, create_state, evaluate, field_decimal, field_value, prepare,
    zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use transient_crypto::{
    curve::{EmbeddedFr, EmbeddedGroupAffine, Fr},
    fab::AlignedValueExt,
};

const PLAN: &str = include_str!(
    "fixtures/generic-state/issue70-derived-crypto/321/Issue70DerivedCrypto.encrypt.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "fixtures/generic-state/issue70-derived-crypto/321/Issue70DerivedCrypto.encrypt.zkir"
);

fn hash(parts: &[&[u8]]) -> [u8; 32] {
    let mut digest = Sha256::new();
    for part in parts {
        digest.update(part);
    }
    digest.finalize().into()
}
fn tag(text: &str) -> [u8; 32] {
    let mut padded = [0; 32];
    padded[..text.len()].copy_from_slice(text.as_bytes());
    padded
}
fn scalar(parts: &[&[u8]]) -> EmbeddedFr {
    EmbeddedFr::from_le_bytes(&hash(parts)[..31]).unwrap()
}
fn mask(shared: EmbeddedGroupAffine) -> Fr {
    // FAB point preimage is two canonical Native fields, not compressed point bytes.
    let digest = hash(&[
        &shared.x().unwrap().as_le_bytes(),
        &shared.y().unwrap().as_le_bytes(),
    ]);
    let expanded = hash(&[&digest, &tag("Noctium:memo:amount")]);
    Fr::from_le_bytes(&expanded[..31]).unwrap()
}
fn bytes(value: &[u8; 32]) -> Json {
    json!({"kind":"bytes","values":value.as_slice()})
}
fn fixture(
    account_secret: [u8; 32],
    encryption_secret: [u8; 32],
    seed: [u8; 32],
    amount: u64,
) -> (BTreeMap<String, Json>, [u8; 32], Vec<Fr>) {
    let generator = EmbeddedGroupAffine::generator();
    let key = scalar(&[&tag("ElGamal:secretToScalar"), &encryption_secret]);
    let r = scalar(&[&seed, &tag("Noctium:balance")]);
    let e = scalar(&[&seed, &tag("Noctium:memo")]);
    let pk = generator * key;
    let c1 = generator * r;
    let c2 = generator * EmbeddedFr(EmbeddedFr::from(amount).0 + r.0 * key.0);
    let ephemeral = generator * e;
    let shared = generator * EmbeddedFr(e.0 * key.0);
    assert_eq!(shared, ephemeral * key);
    let memo = Fr::from(amount) + mask(shared);
    assert_eq!(memo - mask(ephemeral * key), Fr::from(amount));
    assert_ne!(
        memo - mask(ephemeral * EmbeddedFr::from(9u64)),
        Fr::from(amount)
    );
    let account = hash(&[&account_secret]);
    let inputs = BTreeMap::from([
        ("accountSecret".into(), bytes(&account_secret)),
        ("encryptionSecret".into(), bytes(&encryption_secret)),
        ("seed".into(), bytes(&seed)),
        ("amount".into(), json!(amount.to_string())),
        ("account".into(), bytes(&account)),
        (
            "pk".into(),
            json!({"kind":"jubjubPoint", "x":field_decimal(pk.x().unwrap()), "y":field_decimal(pk.y().unwrap())}),
        ),
    ]);
    let fields = vec![
        c1.x().unwrap(),
        c1.y().unwrap(),
        c2.x().unwrap(),
        c2.y().unwrap(),
        ephemeral.x().unwrap(),
        ephemeral.y().unwrap(),
        memo,
    ];
    (inputs, account, fields)
}
fn record(state: &ChargedState<Db>, account: &[u8; 32], expected: &[Fr], count: usize) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(records) = array.get(0).unwrap() else {
        panic!("expected records map")
    };
    assert_eq!(records.size(), count);
    let cell = records.get(&AlignedValue::from(*account)).unwrap();
    let StateValue::Cell(cell) = &*cell else {
        panic!("expected encrypted record")
    };
    let parts: Vec<_> = expected.iter().map(|value| field_value(*value)).collect();
    assert_eq!(**cell, AlignedValue::concat(&parts));
    let mut fields = Vec::new();
    cell.value_only_field_repr(&mut fields);
    assert_eq!(fields, expected);
}

#[test]
fn derived_keys_elgamal_and_ecdh_memo_match_raw_sha256_preimages() {
    let identity_preimage: Expr = serde_json::from_value(json!({
        "tag":"persistentHashNativeVector", "values":[
            {"tag":"constant","value":"0"}, {"tag":"constant","value":"1"}
        ]
    }))
    .unwrap();
    assert_eq!(
        evaluate(&identity_preimage, &BTreeMap::new()).unwrap(),
        Value::Bytes(
            hex::decode("cb592844121d926f1ca3ad4e1d6fb9d8e260ed6e3216361f7732e975a0e8bbf6")
                .unwrap()
        )
    );
    for length in [0, 33] {
        let invalid = Expr::PersistentHashNativeVector {
            values: vec![Expr::Constant { value: "0".into() }; length],
        };
        assert!(evaluate(&invalid, &BTreeMap::new()).is_err());
    }
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("records".into(), json!([]))])).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    // Public deterministic test material. This does not establish production seed freshness.
    let (inputs, account, fields) = fixture([17; 32], [7; 32], [11; 32], 3);
    let first = prepare(&plan, &inputs, &initial, params, address).unwrap();
    assert_eq!(check(&first, &circuit).unwrap(), first.activity_schedule);
    record(&first.after.state, &account, &fields, 1);
    let (second_inputs, second_account, second_fields) = fixture([18; 32], [8; 32], [12; 32], 0);
    let mut second = prepare(&plan, &second_inputs, &first.after.state, params, address).unwrap();
    assert_eq!(check(&second, &circuit).unwrap(), second.activity_schedule);
    record(&second.after.state, &account, &fields, 2);
    record(&second.after.state, &second_account, &second_fields, 2);
    // The final private transcript value is the bounded plaintext after the three byte secrets.
    assert_eq!(second.preimage.private_transcript.len(), 97);
    *second.preimage.private_transcript.last_mut().unwrap() = Fr::from(1u64);
    assert!(check(&second, &circuit).is_err());
    let mut wrong_high_byte = account;
    wrong_high_byte[31] ^= 1;
    for (name, replacement) in [
        ("encryptionSecret", bytes(&[9; 32])),
        ("accountSecret", bytes(&[19; 32])),
        ("account", bytes(&wrong_high_byte)),
    ] {
        let mut dishonest = inputs.clone();
        dishonest.insert(name.into(), replacement);
        if let Ok(execution) = prepare(&plan, &dishonest, &initial, params, address) {
            assert!(check(&execution, &circuit).is_err());
        }
    }
}

#[test]
#[ignore = "requires fresh Issue70DerivedCrypto artifacts in NOCTIUM_ISSUE70_ARTIFACTS"]
fn source_generated_outputs_match_pinned_compact_crypto_vectors() {
    // OpenZeppelin Compact Contracts f85f1a23685c6bbedfc8c2589ae3aa128aff7c46:
    // EcdhMask.test.ts fixes the ECDH memo fields. The ElGamal.test.ts fixture
    // fixes the public `elgamal-ek-A` bytes; its account ID and tagged scalar
    // below were independently evaluated with Compact Runtime 0.21.0.
    let directory = std::path::PathBuf::from(
        std::env::var_os("NOCTIUM_ISSUE70_ARTIFACTS")
            .expect("set NOCTIUM_ISSUE70_ARTIFACTS to fresh Lean outputs"),
    );
    let plan: Plan = serde_json::from_slice(
        &std::fs::read(directory.join("Issue70DerivedCrypto.referenceVectors.impact.json"))
            .unwrap(),
    )
    .unwrap();
    let circuit = IrSource::load(
        std::fs::read(directory.join("Issue70DerivedCrypto.referenceVectors.zkir"))
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("records".into(), json!([]))])).unwrap();
    let execution = prepare(
        &plan,
        &BTreeMap::new(),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).unwrap();

    let account_id: [u8; 32] =
        hex::decode("1d6fbde974afdb88bda3bae6e6dc2073b030adf2f05c9054d97b5d8faa35aae4")
            .unwrap()
            .try_into()
            .unwrap();
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("accountId".into(), bytes(&account_id)),
            (
                "encryptionScalar".into(),
                json!(
                    "250322812713579579621899596562153863259832695080365813512919770294328632064"
                ),
            ),
            (
                "ephemeralX".into(),
                json!(
                    "29744007854499136538279777804045376227924513599493318762246204369493933045815"
                ),
            ),
            (
                "ephemeralY".into(),
                json!(
                    "2604409624680019572520314011984821445135836579833696274586703556773097648664"
                ),
            ),
            (
                "ciphertext".into(),
                json!("92943607126214901997092911019500281461782473933829915198787051090573790098"),
            ),
        ])
    );
}
