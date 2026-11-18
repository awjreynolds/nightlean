#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Plan, Value, check,
    constructor::construct_state,
    field_value,
    foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue},
    prepare,
    zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use storage::arena::Sp;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str = include_str!("fixtures/foreign-tree/321/ForeignTree.update.impact.json");
const CIRCUIT: &[u8] = include_bytes!("fixtures/foreign-tree/321/ForeignTree.update.zkir");
const SCALAR: ForeignType = ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Scalar);
const CURVE_POINT: ForeignType = ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Point);
const SECP_POINT: ForeignType = ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Point);

fn slot(plan: &Plan, name: &str) -> usize {
    plan.state
        .iter()
        .position(|decl| decl.name == name)
        .unwrap()
}

fn values(round: u8) -> [ForeignValue; 3] {
    let mut scalar = [0; 32];
    scalar[0] = round;
    scalar[25] = 1;
    let curve_point = if round == 2 {
        ForeignValue::zero(CURVE_POINT).unwrap()
    } else {
        let mut generator = [0x66; 32];
        generator[0] = 0x58;
        ForeignValue::from_bytes(CURVE_POINT, &generator).unwrap()
    };
    let secp_point = if round == 2 {
        ForeignValue::zero(SECP_POINT).unwrap()
    } else {
        ForeignValue::from_bytes(
            SECP_POINT,
            &hex::decode("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
                .unwrap(),
        )
        .unwrap()
    };
    [
        ForeignValue::from_bytes(SCALAR, &scalar).unwrap(),
        curve_point,
        secp_point,
    ]
}

fn inputs(domain: &[u8; 32], values: &[ForeignValue; 3]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), json!("7")),
        (
            "domain".into(),
            json!({"kind":"bytes", "values":domain.as_slice()}),
        ),
        (
            "scalar".into(),
            Value::Foreign(values[0].clone()).public_json(),
        ),
        (
            "curvePoint".into(),
            Value::Foreign(values[1].clone()).public_json(),
        ),
        (
            "secpPoint".into(),
            Value::Foreign(values[2].clone()).public_json(),
        ),
    ])
}

fn expected_returns(
    previous: Option<&[ForeignValue; 3]>,
    current: &[ForeignValue; 3],
) -> BTreeMap<String, Json> {
    let defaults = [
        ForeignValue::zero(SCALAR).unwrap(),
        ForeignValue::zero(CURVE_POINT).unwrap(),
        ForeignValue::zero(SECP_POINT).unwrap(),
    ];
    let previous = previous.unwrap_or(&defaults);
    BTreeMap::from([
        (
            "oldScalar".into(),
            Value::Foreign(previous[0].clone()).public_json(),
        ),
        (
            "oldCurvePoint".into(),
            Value::Foreign(previous[1].clone()).public_json(),
        ),
        (
            "oldSecpPoint".into(),
            Value::Foreign(previous[2].clone()).public_json(),
        ),
        (
            "newScalar".into(),
            Value::Foreign(current[0].clone()).public_json(),
        ),
        (
            "newCurvePoint".into(),
            Value::Foreign(current[1].clone()).public_json(),
        ),
        (
            "newSecpPoint".into(),
            Value::Foreign(current[2].clone()).public_json(),
        ),
    ])
}

fn foreign_cell(value: &StateValue<Db>, ty: ForeignType) -> Json {
    let StateValue::Cell(value) = value else {
        panic!("expected a foreign leaf cell")
    };
    let mut fields = Vec::new();
    value.value_only_field_repr(&mut fields);
    let decoded = ForeignValue::decode(ty, &fields).unwrap();
    let atoms: Vec<_> = decoded
        .encode()
        .unwrap()
        .into_iter()
        .map(field_value)
        .collect();
    assert_eq!(**value, AlignedValue::concat(atoms.iter()));
    Value::Foreign(decoded).public_json()
}

fn assert_tree_leaf(
    state: &ChargedState<Db>,
    slot: usize,
    outer_key: &AlignedValue,
    inner_key: &AlignedValue,
    ty: ForeignType,
    expected: &ForeignValue,
) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(outer) = &*array.get(slot).unwrap() else {
        panic!("expected outer tree map")
    };
    let parent = outer.get(outer_key).expect("outer tree key exists");
    let StateValue::Map(inner) = &*parent else {
        panic!("expected inner tree map")
    };
    let leaf = inner.get(inner_key).expect("foreign leaf exists");
    assert_eq!(
        foreign_cell(&leaf, ty),
        Value::Foreign(expected.clone()).public_json()
    );
}

fn assert_tree_sizes(
    state: &ChargedState<Db>,
    slot: usize,
    outer_key: &AlignedValue,
    outer_size: usize,
    inner_size: usize,
) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(outer) = &*array.get(slot).unwrap() else {
        panic!("expected outer tree map")
    };
    assert_eq!(outer.size(), outer_size);
    let parent = outer.get(outer_key).expect("outer tree key exists");
    let StateValue::Map(inner) = &*parent else {
        panic!("expected inner tree map")
    };
    assert_eq!(inner.size(), inner_size);
}

fn replace_nested_cell(
    state: &ChargedState<Db>,
    slot: usize,
    outer_key: &AlignedValue,
    inner_key: &AlignedValue,
    fields: &[Fr],
) -> ChargedState<Db> {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(outer) = &*array.get(slot).unwrap() else {
        panic!("expected outer tree map")
    };
    let parent = outer.get(outer_key).expect("outer tree key exists");
    let StateValue::Map(inner) = &*parent else {
        panic!("expected inner tree map")
    };
    let atoms: Vec<_> = fields.iter().copied().map(field_value).collect();
    let cell = StateValue::Cell(Sp::new(AlignedValue::concat(atoms.iter())));
    let inner = inner.insert(inner_key.clone(), cell);
    let outer = outer.insert(outer_key.clone(), StateValue::Map(inner));
    ChargedState::new(StateValue::Array(
        array.insert(slot, StateValue::Map(outer)).unwrap(),
    ))
}

#[test]
fn foreign_tree_leaves_roundtrip_on_nested_native_maps() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let initial = construct_state(&plan, &BTreeMap::new()).unwrap();
    let scalar_slot = slot(&plan, "scalars");
    let curve_slot = slot(&plan, "curvePoints");
    let secp_slot = slot(&plan, "secpPoints");
    let owner_key = field_value(Fr::from(7u64));
    let domain_a = [0xa1; 32];
    let domain_b = [0xb2; 32];
    let domain_a_key: AlignedValue = domain_a.into();
    let domain_b_key: AlignedValue = domain_b.into();
    let mut point_key_bytes = [0; 32];
    point_key_bytes[..5].copy_from_slice(b"point");
    let point_key: AlignedValue = point_key_bytes.into();

    let first_values = values(1);
    let mut first = prepare(
        &plan,
        &inputs(&domain_a, &first_values),
        &initial,
        params,
        address,
    )
    .unwrap();
    assert_eq!(first.returns_json(), expected_returns(None, &first_values));
    assert_eq!(check(&first, &circuit).unwrap(), first.activity_schedule);
    let original = first.preimage.public_transcript_outputs[0];
    first.preimage.public_transcript_outputs[0] = original + Fr::from(1u64);
    assert!(check(&first, &circuit).is_err());
    let state_a = first.after.state.clone();
    assert_tree_sizes(&state_a, scalar_slot, &owner_key, 1, 1);
    assert_tree_sizes(&state_a, curve_slot, &domain_a_key, 1, 1);
    assert_tree_sizes(&state_a, secp_slot, &domain_a_key, 1, 1);
    assert_tree_leaf(
        &state_a,
        scalar_slot,
        &owner_key,
        &domain_a_key,
        SCALAR,
        &first_values[0],
    );
    assert_tree_leaf(
        &state_a,
        curve_slot,
        &domain_a_key,
        &owner_key,
        CURVE_POINT,
        &first_values[1],
    );
    assert_tree_leaf(
        &state_a,
        secp_slot,
        &domain_a_key,
        &point_key,
        SECP_POINT,
        &first_values[2],
    );

    let second_values = values(2);
    let second = prepare(
        &plan,
        &inputs(&domain_a, &second_values),
        &state_a,
        params,
        address,
    )
    .unwrap();
    assert_eq!(
        second.returns_json(),
        expected_returns(Some(&first_values), &second_values)
    );
    assert_eq!(check(&second, &circuit).unwrap(), second.activity_schedule);
    let state_a = second.after.state.clone();
    assert_tree_sizes(&state_a, scalar_slot, &owner_key, 1, 1);
    assert_tree_sizes(&state_a, curve_slot, &domain_a_key, 1, 1);
    assert_tree_sizes(&state_a, secp_slot, &domain_a_key, 1, 1);
    assert_tree_leaf(
        &state_a,
        scalar_slot,
        &owner_key,
        &domain_a_key,
        SCALAR,
        &second_values[0],
    );
    assert_tree_leaf(
        &state_a,
        curve_slot,
        &domain_a_key,
        &owner_key,
        CURVE_POINT,
        &second_values[1],
    );
    assert_tree_leaf(
        &state_a,
        secp_slot,
        &domain_a_key,
        &point_key,
        SECP_POINT,
        &second_values[2],
    );

    let third_values = values(3);
    let third = prepare(
        &plan,
        &inputs(&domain_b, &third_values),
        &state_a,
        params,
        address,
    )
    .unwrap();
    assert_eq!(third.returns_json(), expected_returns(None, &third_values));
    assert_eq!(check(&third, &circuit).unwrap(), third.activity_schedule);
    let state_ab = &third.after.state;
    assert_tree_sizes(state_ab, scalar_slot, &owner_key, 1, 2);
    assert_tree_sizes(state_ab, curve_slot, &domain_a_key, 2, 1);
    assert_tree_sizes(state_ab, curve_slot, &domain_b_key, 2, 1);
    assert_tree_sizes(state_ab, secp_slot, &domain_a_key, 2, 1);
    assert_tree_sizes(state_ab, secp_slot, &domain_b_key, 2, 1);
    assert_tree_leaf(
        state_ab,
        scalar_slot,
        &owner_key,
        &domain_a_key,
        SCALAR,
        &second_values[0],
    );
    assert_tree_leaf(
        state_ab,
        scalar_slot,
        &owner_key,
        &domain_b_key,
        SCALAR,
        &third_values[0],
    );
    assert_tree_leaf(
        state_ab,
        curve_slot,
        &domain_a_key,
        &owner_key,
        CURVE_POINT,
        &second_values[1],
    );
    assert_tree_leaf(
        state_ab,
        curve_slot,
        &domain_b_key,
        &owner_key,
        CURVE_POINT,
        &third_values[1],
    );
    assert_tree_leaf(
        state_ab,
        secp_slot,
        &domain_a_key,
        &point_key,
        SECP_POINT,
        &second_values[2],
    );
    assert_tree_leaf(
        state_ab,
        secp_slot,
        &domain_b_key,
        &point_key,
        SECP_POINT,
        &third_values[2],
    );

    let malformed = replace_nested_cell(
        &state_a,
        scalar_slot,
        &owner_key,
        &domain_a_key,
        &[Fr::from(1u64)],
    );
    assert!(
        prepare(
            &plan,
            &inputs(&domain_a, &third_values),
            &malformed,
            params,
            address,
        )
        .is_err()
    );

    let mut wrong_role = plan.clone();
    wrong_role.state[scalar_slot].kind["tree"]["map"][1]["map"][1]["scalar"] =
        json!("Curve25519Base");
    assert!(
        prepare(
            &wrong_role,
            &inputs(&domain_a, &third_values),
            &state_a,
            params,
            address,
        )
        .is_err()
    );

    let mut foreign_key = plan;
    foreign_key.state[scalar_slot].kind["tree"]["map"][0] = json!("Curve25519Scalar");
    assert!(construct_state(&foreign_key, &BTreeMap::new()).is_err());
}
