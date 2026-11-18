#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Expr, Plan, Value, check, create_state, evaluate, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str = include_str!(
    "fixtures/generic-state/issue70-hash-preimages/321/Issue70HashPreimages.register.impact.json"
);
const CIRCUIT: &[u8] = include_bytes!(
    "fixtures/generic-state/issue70-hash-preimages/321/Issue70HashPreimages.register.zkir"
);

fn digest(text: &str) -> [u8; 32] {
    hex::decode(text).unwrap().try_into().unwrap()
}

fn inputs(secret: &[u8; 32], key: &[u8; 32], credit: &[u8; 32]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        (
            "secret".into(),
            json!({"kind":"bytes","values":secret.as_slice()}),
        ),
        ("count".into(), json!("7")),
        (
            "expectedKey".into(),
            json!({"kind":"bytes","values":key.as_slice()}),
        ),
        (
            "expectedCredit".into(),
            json!({"kind":"bytes","values":credit.as_slice()}),
        ),
    ])
}

fn assert_keys(state: &ChargedState<Db>, keys: &[[u8; 32]]) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(registered) = array.get(0).unwrap() else {
        panic!("expected map")
    };
    assert_eq!(registered.size(), keys.len());
    for key in keys {
        let key: AlignedValue = (*key).into();
        let marker = registered
            .get(&key)
            .expect("exact independently calculated hash key");
        let StateValue::Cell(marker) = &*marker else {
            panic!("expected marker cell")
        };
        let mut fields = Vec::new();
        marker.value_only_field_repr(&mut fields);
        assert_eq!(fields, vec![Fr::from(1u64)]);
    }
}

#[test]
fn source_ordered_hash_preimages_match_native_vectors_and_bind_keys() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("registered".into(), json!([]))])).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let zero = [0u8; 32];
    let ascending = std::array::from_fn(|index| index as u8);
    // Python hashlib over exact padded UTF8 tags, ordered raw byte slots, and count=7 LE32.
    let zero_key = digest("6c0609b88d600d1406a55b00726f0b4346da61abeb0ff2bc0fae1037ac530682");
    let zero_credit = digest("013fb15223ec786f3d6508e2f32c9d1b1c43bc4c68ae412eb8eada3bc9530e21");
    let ascending_key = digest("cb31bae1ff2ceb9608d89993ae58d354b0df1d12c971f1c84860e75f47940be2");
    let ascending_credit =
        digest("2386385597902f0b3e897315ba4056ccd2bc189552cc93b862214624cb07fbc5");
    let first = prepare(
        &plan,
        &inputs(&zero, &zero_key, &zero_credit),
        &initial,
        params,
        address,
    )
    .unwrap();
    assert_eq!(check(&first, &circuit).unwrap(), first.activity_schedule);
    assert_keys(&first.after.state, &[zero_key, zero_credit]);
    let mut second = prepare(
        &plan,
        &inputs(&ascending, &ascending_key, &ascending_credit),
        &first.after.state,
        params,
        address,
    )
    .unwrap();
    assert_eq!(check(&second, &circuit).unwrap(), second.activity_schedule);
    assert_keys(
        &second.after.state,
        &[zero_key, zero_credit, ascending_key, ascending_credit],
    );

    let reversed = digest("ae826922b7f31441f9a9c3a84f6daf6b66e939190675fad84f341782e4aeda84");
    if let Ok(execution) = prepare(
        &plan,
        &inputs(&zero, &reversed, &zero_credit),
        &initial,
        params,
        address,
    ) {
        assert!(check(&execution, &circuit).is_err());
    }
    // Change the private Native count, retaining the published keys and VM transcript.
    assert_eq!(second.preimage.private_transcript.len(), 33);
    second.preimage.private_transcript[32] = Fr::from(8u64);
    assert!(check(&second, &circuit).is_err());

    let native: Expr = serde_json::from_value(
        json!({"tag":"persistentHashNative","value":{"tag":"constant","value":"7"}}),
    )
    .unwrap();
    assert_eq!(
        evaluate(&native, &BTreeMap::new()).unwrap(),
        Value::Bytes(
            digest("f5411ec7e51e46159c654bdbdf3cc20785a217b87384810ed2e541dc0016943a").to_vec()
        )
    );
    let bad_literal = Expr::Bytes32Literal {
        values: vec![0; 31],
    };
    assert!(evaluate(&bad_literal, &BTreeMap::new()).is_err());
    for values in [
        vec![],
        vec![
            Expr::Bytes32Literal {
                values: vec![0; 32]
            };
            33
        ],
    ] {
        assert!(evaluate(&Expr::PersistentHashVector32 { values }, &BTreeMap::new()).is_err());
    }
    assert!(
        evaluate(
            &Expr::PersistentHashNative {
                value: Box::new(Expr::Bool { value: true })
            },
            &BTreeMap::new()
        )
        .is_err()
    );
    assert!(
        serde_json::from_value::<Expr>(json!({"tag":"bytes32Literal","values":vec![256;32]}))
            .is_err()
    );
}
