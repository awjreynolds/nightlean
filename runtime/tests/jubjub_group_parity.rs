#![cfg(feature = "zkir-321")]

use noctium_runtime::{Plan, check, create_state, field_decimal, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};
use transient_crypto::curve::{EmbeddedFr, EmbeddedGroupAffine};

fn artifact_directory() -> PathBuf {
    PathBuf::from(
        env::var_os("NOCTIUM_JUBJUB_GROUP_PARITY_DIR")
            .expect("NOCTIUM_JUBJUB_GROUP_PARITY_DIR must point to fresh Lean outputs"),
    )
}

#[test]
#[ignore = "requires fresh JubjubGroupParity artifacts in NOCTIUM_JUBJUB_GROUP_PARITY_DIR"]
fn native_jubjub_group_operations_match_compact_group_parity() -> anyhow::Result<()> {
    let directory = artifact_directory();
    let plan: Plan = serde_json::from_slice(&fs::read(
        directory.join("JubjubGroupParity.groupParity.impact.json"),
    )?)?;
    let circuit =
        IrSource::load(fs::read(directory.join("JubjubGroupParity.groupParity.zkir"))?.as_slice())?;
    let initial = create_state(&plan, &BTreeMap::new())?;
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    let point = EmbeddedGroupAffine::generator();
    let identity = EmbeddedGroupAffine::identity();
    let scalar = EmbeddedFr::from(1u64);
    let [point_x, point_y] = [point.x().unwrap(), point.y().unwrap()];
    let inputs = BTreeMap::<String, Json>::from([
        ("pointX".into(), json!(field_decimal(point_x))),
        ("pointY".into(), json!(field_decimal(point_y))),
        ("rawScalar".into(), json!("1")),
    ]);

    let execution = prepare(&plan, &inputs, &initial, parameters, address)?;
    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);

    let generated = EmbeddedGroupAffine::generator() * scalar;
    let multiplied = point * scalar;
    let sum = point + identity;
    let negated = -point;
    let cancelled = point + negated;
    let identity_negated = -identity;
    let coordinates =
        |value: EmbeddedGroupAffine| [value.x().unwrap(), value.y().unwrap()].map(field_decimal);
    let [checked_x, checked_y] = coordinates(point);
    let [generator_x, generator_y] = coordinates(generated);
    let [multiplied_x, multiplied_y] = coordinates(multiplied);
    let [sum_x, sum_y] = coordinates(sum);
    let [negated_x, negated_y] = coordinates(negated);
    let [cancelled_x, cancelled_y] = coordinates(cancelled);
    let [identity_negated_x, identity_negated_y] = coordinates(identity_negated);

    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("resultCheckedX".into(), json!(checked_x)),
            ("resultCheckedY".into(), json!(checked_y)),
            ("resultGeneratorX".into(), json!(generator_x)),
            ("resultGeneratorY".into(), json!(generator_y)),
            ("resultMultipliedX".into(), json!(multiplied_x)),
            ("resultMultipliedY".into(), json!(multiplied_y)),
            ("resultSumX".into(), json!(sum_x)),
            ("resultSumY".into(), json!(sum_y)),
            ("resultNegatedX".into(), json!(negated_x)),
            ("resultNegatedY".into(), json!(negated_y)),
            ("resultCancelledX".into(), json!(cancelled_x)),
            ("resultCancelledY".into(), json!(cancelled_y)),
            ("resultIdentityNegatedX".into(), json!(identity_negated_x)),
            ("resultIdentityNegatedY".into(), json!(identity_negated_y)),
            ("resultScalar".into(), json!("1")),
        ])
    );
    assert_eq!(sum, point, "adding the identity preserves the point");
    assert_eq!(cancelled, identity, "a point plus its negation is identity");
    assert_eq!(
        identity_negated, identity,
        "negating identity preserves identity"
    );
    Ok(())
}
