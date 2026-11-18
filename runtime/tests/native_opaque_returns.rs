#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Expr, Plan, check, create_state, field_decimal, field_value, prepare, zkir::IrSource,
};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use transient_crypto::{
    curve::{EmbeddedFr, EmbeddedGroupAffine, Fr},
    fab::AlignedValueExt,
};

fn inputs(secret: [u8; 32], scalar: &str) -> BTreeMap<String, Json> {
    BTreeMap::from([
        (
            "secret".into(),
            json!({"kind":"bytes", "values":secret.as_slice()}),
        ),
        (
            "scalar".into(),
            json!({"kind":"jubjubScalar", "value":scalar}),
        ),
        ("enabled".into(), json!(true)),
    ])
}

#[test]
fn opaque_getter_returns_match_sha_curve_and_full_width_commitments() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/native-opaque-returns/321/NativeOpaqueReturns.compute.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/native-opaque-returns/321/NativeOpaqueReturns.compute.zkir")
            .as_slice(),
    )
    .unwrap();
    let state = create_state(&plan, &BTreeMap::from([("marker".into(), json!("0"))])).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let mut last_secret = [0u8; 32];
    let mut last_digest = [0u8; 32];
    let maximum = "6554484396890773809930967563523245729705921265872317281365359162392183254198";
    for (secret, scalar_text, scalar) in [
        ([0u8; 32], "7", EmbeddedFr::from(7u64)),
        ([9u8; 32], maximum, -EmbeddedFr::from(1u64)),
    ] {
        let execution =
            prepare(&plan, &inputs(secret, scalar_text), &state, params, address).unwrap();
        check(&execution, &circuit).unwrap();
        let digest: [u8; 32] = Sha256::digest(secret).into();
        let point = EmbeddedGroupAffine::generator() * scalar;
        let x = point.x().unwrap();
        let y = point.y().unwrap();
        assert_eq!(
            execution.returns_json(),
            BTreeMap::from([
                (
                    "digest".into(),
                    json!({"kind":"bytes","values":digest.as_slice()})
                ),
                (
                    "scalarValue".into(),
                    json!({"kind":"jubjubScalar","value":scalar_text})
                ),
                (
                    "pointValue".into(),
                    json!({"kind":"jubjubPoint","x":field_decimal(x),"y":field_decimal(y)})
                ),
                ("markerValue".into(), json!("7")),
            ])
        );
        let mut fields = Vec::new();
        AlignedValue::from(digest).value_only_field_repr(&mut fields);
        fields.extend([
            noctium_runtime::canonical_field(scalar_text).unwrap(),
            x,
            y,
            Fr::from(7u64),
        ]);
        assert_eq!(fields.len(), 6);
        let fields: Vec<_> = fields.into_iter().map(field_value).collect();
        let (commitment, randomness) = execution.preimage.communications_commitment.unwrap();
        assert_eq!(
            commitment,
            onchain_runtime::communication_commitment(
                AlignedValue::concat(std::iter::empty::<&AlignedValue>()),
                AlignedValue::concat(&fields),
                randomness
            )
        );
        last_secret = secret;
        last_digest = digest;
    }
    let mut forged = plan.clone();
    last_digest[31] ^= 1;
    forged.returns[0].expression = Expr::Bytes32Literal {
        values: last_digest.to_vec(),
    };
    let execution = prepare(
        &forged,
        &inputs(last_secret, maximum),
        &state,
        params,
        address,
    )
    .unwrap();
    assert!(execution.preimage.check(&circuit).is_err());
    assert!(check(&execution, &circuit).is_err());
}
