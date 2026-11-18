#![cfg(feature = "zkir-321")]

use noctium_runtime::zkir::IrSource;
use noctium_runtime::{Expr, Plan, Value, check, create_state, prepare};
use serde_json::json;
use std::collections::BTreeMap;
use transient_crypto::{
    curve::{EmbeddedFr, EmbeddedGroupAffine, Fr},
    hash::hash_to_curve,
};

#[test]
fn native_hash_to_curve_binds_ordered_fields_and_typed_results() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/hash-to-curve/321/HashToCurve.inspect.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/hash-to-curve/321/HashToCurve.inspect.zkir").as_slice(),
    )
    .unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    for (left, right) in [(3u64, 5u64), (7, 11)] {
        let inputs = BTreeMap::from([
            ("left".into(), json!(left.to_string())),
            ("right".into(), json!(right.to_string())),
            ("enabled".into(), json!(true)),
        ]);
        let mut execution = prepare(
            &plan,
            &inputs,
            &initial,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        let empty = hash_to_curve(&[] as &[Fr]);
        let one = hash_to_curve(&[Fr::from(left)][..]);
        let domain = hash_to_curve(&[Fr::from(17u64), Fr::from(left), Fr::from(right)][..]);
        let composed = domain + EmbeddedGroupAffine::generator() * EmbeddedFr::from(right);
        let mut encoded: [u8; 32] = composed.y().unwrap().as_le_bytes().try_into().unwrap();
        encoded[31] |= (composed.x().unwrap().as_le_bytes()[0] & 1) << 7;
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([
                ("emptyPoint".into(), Value::JubjubPoint(empty).public_json()),
                ("onePoint".into(), Value::JubjubPoint(one).public_json()),
                (
                    "domainPoint".into(),
                    Value::JubjubPoint(domain).public_json()
                ),
                (
                    "composedPoint".into(),
                    Value::JubjubPoint(composed).public_json()
                ),
                (
                    "encodedPoint".into(),
                    json!({"kind":"bytes","values":encoded.to_vec()})
                ),
                (
                    "scalarResult".into(),
                    Value::JubjubScalar(EmbeddedFr::from(right)).public_json()
                ),
            ])
        );
        execution.preimage.private_transcript[1] = Fr::from(right + 1);
        assert!(check(&execution, &circuit).is_err());
        execution.preimage.private_transcript[1] = Fr::from(right);
        execution.preimage.private_transcript[2] = Fr::from(0u64);
        assert!(check(&execution, &circuit).is_err());
        for fields in [[17, right, left], [18, left, right]] {
            let mut forged = plan.clone();
            forged.returns[2].expression = Expr::HashToCurve {
                values: fields
                    .into_iter()
                    .map(|value| Expr::Constant {
                        value: value.to_string(),
                    })
                    .collect(),
            };
            let forged = prepare(
                &forged,
                &inputs,
                &initial,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )
            .unwrap();
            assert!(check(&forged, &circuit).is_err());
        }
    }
}
