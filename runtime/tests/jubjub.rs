#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Expr, MODULUS, Plan, ScalarType, Value, check, create_state, environment, evaluate,
    field_decimal, field_value, prepare, zkir::IrSource,
};
use num_bigint::BigUint;
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{
    curve::{EmbeddedFr, EmbeddedGroupAffine, Fr},
    fab::AlignedValueExt,
};

const PLAN: &str =
    include_str!("fixtures/generic-state/issue70-jubjub/321/Issue70Jubjub.encrypt.impact.json");
const CIRCUIT: &[u8] =
    include_bytes!("fixtures/generic-state/issue70-jubjub/321/Issue70Jubjub.encrypt.zkir");
const ORDER: &str = "6554484396890773809930967563523245729705921265872317281365359162392183254199";

fn scalar(value: &str) -> Json {
    json!({"kind":"jubjubScalar","value":value})
}
fn point(value: EmbeddedGroupAffine) -> Json {
    json!({"kind":"jubjubPoint","x":field_decimal(value.x().unwrap()),"y":field_decimal(value.y().unwrap())})
}
fn inputs(account: &[u8; 32], message: u64) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("sk".into(), scalar("7")),
        ("r".into(), scalar("11")),
        ("message".into(), scalar(&message.to_string())),
        (
            "pk".into(),
            point(EmbeddedGroupAffine::generator() * EmbeddedFr::from(7u64)),
        ),
        (
            "account".into(),
            json!({"kind":"bytes","values":account.as_slice()}),
        ),
        ("publicScalar".into(), scalar("13")),
    ])
}
fn fields(value: EmbeddedGroupAffine) -> [Fr; 2] {
    [value.x().unwrap(), value.y().unwrap()]
}
fn assert_ciphertext(
    state: &ChargedState<Db>,
    account: &[u8; 32],
    c2_multiplier: u64,
    count: usize,
) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(map) = array.get(0).unwrap() else {
        panic!("expected ciphertext map")
    };
    assert_eq!(map.size(), count);
    let cell = map.get(&AlignedValue::from(*account)).unwrap();
    let StateValue::Cell(cell) = &*cell else {
        panic!("expected one ciphertext cell")
    };
    let generator = EmbeddedGroupAffine::generator();
    let mut expected = fields(generator * EmbeddedFr::from(11u64)).to_vec();
    expected.extend(fields(generator * EmbeddedFr::from(c2_multiplier)));
    let aligned: Vec<_> = expected.iter().map(|value| field_value(*value)).collect();
    assert_eq!(**cell, AlignedValue::concat(&aligned));
    let mut actual = Vec::new();
    cell.value_only_field_repr(&mut actual);
    assert_eq!(actual, expected);
}
fn rejects(
    plan: &Plan,
    circuit: &IrSource,
    initial: &ChargedState<Db>,
    inputs: &BTreeMap<String, Json>,
) {
    if let Ok(execution) = prepare(
        plan,
        inputs,
        initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    ) {
        assert!(check(&execution, circuit).is_err());
    }
}
#[test]
fn typed_jubjub_elgamal_binds_ciphertext_and_rejects_noncanonical_scalars() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial =
        create_state(&plan, &BTreeMap::from([("ciphertexts".into(), json!([]))])).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let account = [0u8; 32];
    let first = prepare(&plan, &inputs(&account, 3), &initial, params, address).unwrap();
    assert_eq!(check(&first, &circuit).unwrap(), first.activity_schedule);
    // c1=11G, c2=(message 3 + public delta 13 + randomness 11 * key 7)G=93G.
    assert_ciphertext(&first.after.state, &account, 93, 1);
    let other = [1u8; 32];
    let mut second = prepare(
        &plan,
        &inputs(&other, 5),
        &first.after.state,
        params,
        address,
    )
    .unwrap();
    assert_eq!(check(&second, &circuit).unwrap(), second.activity_schedule);
    assert_ciphertext(&second.after.state, &account, 93, 2);
    assert_ciphertext(&second.after.state, &other, 95, 2);

    let upper_account = [2u8; 32];
    let mut upper = inputs(&upper_account, 3);
    let order_minus_one = BigUint::parse_bytes(ORDER.as_bytes(), 10).unwrap() - BigUint::from(1u8);
    upper.insert(
        "publicScalar".into(),
        scalar(&order_minus_one.to_str_radix(10)),
    );
    let upper = prepare(&plan, &upper, &second.after.state, params, address).unwrap();
    assert_eq!(check(&upper, &circuit).unwrap(), upper.activity_schedule);
    assert_ciphertext(&upper.after.state, &upper_account, 79, 3);

    second.preimage.private_transcript[2] = Fr::from(6u64);
    assert!(check(&second, &circuit).is_err());
    second.preimage.private_transcript[2] = Fr::from(5u64);

    let mut wrong_key = inputs(&account, 3);
    wrong_key.insert(
        "pk".into(),
        point(EmbeddedGroupAffine::generator() * EmbeddedFr::from(8u64)),
    );
    rejects(&plan, &circuit, &initial, &wrong_key);
    let mut zero_randomness = inputs(&account, 3);
    zero_randomness.insert("r".into(), scalar("0"));
    rejects(&plan, &circuit, &initial, &zero_randomness);
    let mut identity_key = inputs(&account, 3);
    identity_key.insert("pk".into(), point(EmbeddedGroupAffine::identity()));
    rejects(&plan, &circuit, &initial, &identity_key);

    // q+7 has the same reduced scalar as 7, but is forbidden by the typed-input roundtrip constraint.
    assert_eq!(second.preimage.private_transcript.len(), 3);
    let aliased = BigUint::parse_bytes(ORDER.as_bytes(), 10).unwrap() + BigUint::from(7u8);
    second.preimage.private_transcript[0] = Fr::from_le_bytes(&aliased.to_bytes_le()).unwrap();
    assert!(check(&second, &circuit).is_err());

    let valid = inputs(&account, 3);
    let public_key = EmbeddedGroupAffine::generator() * EmbeddedFr::from(7u64);
    let mut wrong_coordinate = valid.clone();
    wrong_coordinate.insert(
        "pk".into(),
        json!({
            "kind":"jubjubPoint",
            "x":field_decimal(public_key.x().unwrap() + Fr::from(2u64)),
            "y":field_decimal(public_key.y().unwrap())
        }),
    );
    assert!(environment(&plan, &wrong_coordinate).is_err());
    for invalid in [
        scalar(ORDER),
        scalar("07"),
        json!("7"),
        json!({"kind":"jubjubScalar","value":"7","extra":0}),
    ] {
        let mut bad = valid.clone();
        bad.insert("sk".into(), invalid);
        assert!(environment(&plan, &bad).is_err());
    }
    for invalid in [
        json!({"kind":"jubjubPoint","x":"0","y":"0"}),
        json!({"kind":"jubjubPoint","x":"0","y":(BigUint::parse_bytes(MODULUS.as_bytes(),10).unwrap()-BigUint::from(1u8)).to_str_radix(10)}),
        json!({"kind":"jubjubPoint","x":"00","y":"1"}),
    ] {
        let mut bad = valid.clone();
        bad.insert("pk".into(), invalid);
        assert!(environment(&plan, &bad).is_err());
    }
    let mut identity = valid.clone();
    identity.insert("pk".into(), point(EmbeddedGroupAffine::identity()));
    assert_eq!(
        environment(&plan, &identity).unwrap()["pk"].public_json(),
        identity["pk"]
    );
    assert!(
        Value::JubjubScalar(EmbeddedFr::from(7u64))
            .cast(&ScalarType::Native)
            .is_err()
    );
    assert!(
        Value::Native(Fr::from(7u64))
            .cast(&ScalarType::JubjubScalar)
            .is_err()
    );
    let reduction = Expr::JubjubScalarFromNative {
        value: Box::new(Expr::Constant {
            value: aliased.to_str_radix(10),
        }),
    };
    assert_eq!(
        evaluate(&reduction, &BTreeMap::new()).unwrap(),
        Value::JubjubScalar(EmbeddedFr::from(7u64))
    );

    let digest = Expr::Bytes32Literal {
        values: (0..32).collect(),
    };
    let low31 = Expr::BytesField {
        value: Box::new(digest.clone()),
        index: 1,
    };
    // Independently calculated with Python int.from_bytes(bytes(range(31)), 'little').
    assert_eq!(
        evaluate(&low31, &BTreeMap::new()).unwrap(),
        Value::Native(
            noctium_runtime::canonical_field(
                "53206320320083115796502214552783413060461247639578808291150702859268522240"
            )
            .unwrap()
        )
    );
    assert_eq!(
        evaluate(
            &Expr::BytesField {
                value: Box::new(digest.clone()),
                index: 0
            },
            &BTreeMap::new()
        )
        .unwrap(),
        Value::Native(Fr::from(31u64))
    );
    assert!(
        evaluate(
            &Expr::BytesField {
                value: Box::new(digest),
                index: 2
            },
            &BTreeMap::new()
        )
        .is_err()
    );
}
