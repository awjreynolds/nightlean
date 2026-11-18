#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Environment, Expr, Plan, Value, canonical_field, check, constructor::construct_state,
    evaluate, field_value, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use storage::arena::Sp;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str = include_str!("fixtures/jubjub-storage/321/JubjubStorage.update.impact.json");
const CIRCUIT: &[u8] = include_bytes!("fixtures/jubjub-storage/321/JubjubStorage.update.zkir");
const JUBJUB_ORDER: &str =
    "6554484396890773809930967563523245729705921265872317281365359162392183254199";

fn constant(value: u64) -> Expr {
    Expr::Constant {
        value: value.to_string(),
    }
}

fn scalar_expression(value: u64) -> Expr {
    Expr::JubjubScalarFromNative {
        value: Box::new(constant(value)),
    }
}

fn scalar(value: u64) -> Value {
    evaluate(&scalar_expression(value), &Environment::new()).unwrap()
}

fn point(expression: Expr) -> Value {
    let value = evaluate(&expression, &Environment::new()).unwrap();
    assert!(matches!(&value, Value::JubjubPoint(_)));
    value
}

fn generator() -> Value {
    point(Expr::JubjubMulGenerator {
        scalar: Box::new(scalar_expression(1)),
    })
}

fn identity() -> Value {
    point(Expr::JubjubFromCoordinates {
        x: Box::new(constant(0)),
        y: Box::new(constant(1)),
    })
}

fn doubled_generator() -> Value {
    point(Expr::JubjubMulGenerator {
        scalar: Box::new(scalar_expression(2)),
    })
}

fn values(number: u64, point: Value) -> [Value; 2] {
    [scalar(number), point]
}

fn value_fields(value: &Value) -> Vec<Fr> {
    match value {
        Value::JubjubScalar(_) => {
            vec![canonical_field(value.public_json()["value"].as_str().unwrap()).unwrap()]
        }
        Value::JubjubPoint(point) => vec![
            point.x().expect("Jubjub point has an x coordinate"),
            point.y().expect("Jubjub point has a y coordinate"),
        ],
        _ => panic!("expected a Jubjub value"),
    }
}

fn inputs(owner: u64, domain: &[u8; 32], values: &[Value; 2]) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), json!(owner.to_string())),
        (
            "domain".into(),
            json!({"kind":"bytes", "values":domain.as_slice()}),
        ),
        ("scalar".into(), values[0].public_json()),
        ("point".into(), values[1].public_json()),
    ])
}

fn expected_returns(
    old_cell: [&Value; 2],
    old_map: [&Value; 2],
    old_tree: [&Value; 2],
    current: [&Value; 2],
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("oldScalarCell".into(), old_cell[0].public_json()),
        ("oldPointCell".into(), old_cell[1].public_json()),
        ("oldScalarMap".into(), old_map[0].public_json()),
        ("oldPointMap".into(), old_map[1].public_json()),
        ("oldScalarTree".into(), old_tree[0].public_json()),
        ("oldPointTree".into(), old_tree[1].public_json()),
        ("newScalarCell".into(), current[0].public_json()),
        ("newPointCell".into(), current[1].public_json()),
        ("newScalarMap".into(), current[0].public_json()),
        ("newPointMap".into(), current[1].public_json()),
        ("newScalarTree".into(), current[0].public_json()),
        ("newPointTree".into(), current[1].public_json()),
    ])
}

fn slot(plan: &Plan, name: &str) -> usize {
    plan.state
        .iter()
        .position(|decl| decl.name == name)
        .unwrap()
}

fn assert_cell(value: &StateValue<Db>, expected: &Value) {
    let StateValue::Cell(cell) = value else {
        panic!("expected a Jubjub leaf cell")
    };
    let fields = value_fields(expected);
    assert_eq!(
        fields.len(),
        if matches!(expected, Value::JubjubScalar(_)) {
            1
        } else {
            2
        }
    );
    let mut actual = Vec::new();
    cell.value_only_field_repr(&mut actual);
    assert_eq!(actual, fields);
    let encoded: Vec<_> = fields.iter().copied().map(field_value).collect();
    assert_eq!(**cell, AlignedValue::concat(encoded.iter()));
}

fn assert_direct_cell(state: &ChargedState<Db>, slot: usize, expected: &Value) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    assert_cell(&array.get(slot).unwrap(), expected);
}

fn assert_map_cell(state: &ChargedState<Db>, slot: usize, key: &AlignedValue, expected: &Value) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(map) = &*array.get(slot).unwrap() else {
        panic!("expected map")
    };
    assert_cell(&map.get(key).expect("map key exists"), expected);
}

fn assert_tree_cell(
    state: &ChargedState<Db>,
    slot: usize,
    outer_key: &AlignedValue,
    inner_key: &AlignedValue,
    expected: &Value,
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
    assert_cell(&inner.get(inner_key).expect("tree key exists"), expected);
}

fn assert_map_size(state: &ChargedState<Db>, slot: usize, size: usize) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(map) = &*array.get(slot).unwrap() else {
        panic!("expected map")
    };
    assert_eq!(map.size(), size);
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

fn replace_cell(state: &ChargedState<Db>, slot: usize, fields: &[Fr]) -> ChargedState<Db> {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let encoded: Vec<_> = fields.iter().copied().map(field_value).collect();
    let cell = StateValue::Cell(Sp::new(AlignedValue::concat(encoded.iter())));
    ChargedState::new(StateValue::Array(array.insert(slot, cell).unwrap()))
}

fn assert_rejected(
    plan: &Plan,
    circuit: &IrSource,
    state: &ChargedState<Db>,
    owner: u64,
    domain: &[u8; 32],
    values: &[Value; 2],
) {
    let before = state.clone();
    let supplied = inputs(owner, domain, values);
    if let Ok(execution) = prepare(
        plan,
        &supplied,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    ) {
        assert!(check(&execution, circuit).is_err());
    }
    assert_eq!(state, &before, "failed execution changed caller state");
}

fn assert_rejects_map_key(plan: &Plan, name: &str, key_type: &str) {
    let mut invalid = plan.clone();
    let slot = slot(plan, name);
    invalid.state[slot].kind["map"][0] = json!(key_type);
    assert!(
        construct_state(&invalid, &BTreeMap::new()).is_err(),
        "{name} key"
    );
}

fn assert_rejects_tree_key(plan: &Plan, name: &str, outer: bool, key_type: &str) {
    let mut invalid = plan.clone();
    let slot = slot(plan, name);
    let tree = &mut invalid.state[slot].kind["tree"]["map"];
    let key_index = if outer { 0 } else { 1 };
    if outer {
        tree[key_index] = json!(key_type);
    } else {
        tree[key_index]["map"][0] = json!(key_type);
    }
    assert!(
        construct_state(&invalid, &BTreeMap::new()).is_err(),
        "{name} key"
    );
}

#[test]
fn jubjub_cells_maps_and_trees_roundtrip_through_native_state() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = construct_state(&plan, &BTreeMap::new()).unwrap();
    let before_first = initial.clone();
    let scalar_cell = slot(&plan, "scalarCell");
    let point_cell = slot(&plan, "pointCell");
    let scalar_map = slot(&plan, "scalarMap");
    let point_map = slot(&plan, "pointMap");
    let scalars = slot(&plan, "scalars");
    let points = slot(&plan, "points");
    let owner7 = field_value(Fr::from(7u64));
    let owner9 = field_value(Fr::from(9u64));
    let domain_a = [0xa1; 32];
    let domain_b = [0xb2; 32];
    let domain_a_key: AlignedValue = domain_a.into();
    let domain_b_key: AlignedValue = domain_b.into();

    let defaults = [scalar(0), identity()];
    let first_values = values(3, generator());
    let mut first = prepare(
        &plan,
        &inputs(7, &domain_a, &first_values),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    assert_eq!(
        first.returns_json(),
        expected_returns(
            [&defaults[0], &defaults[1]],
            [&defaults[0], &defaults[1]],
            [&defaults[0], &defaults[1]],
            [&first_values[0], &first_values[1]],
        )
    );
    assert_eq!(check(&first, &circuit).unwrap(), first.activity_schedule);
    let original = first.preimage.public_transcript_outputs[0];
    first.preimage.public_transcript_outputs[0] = original + Fr::from(1u64);
    assert!(check(&first, &circuit).is_err());
    let state_a = first.after.state.clone();
    assert_eq!(initial, before_first);
    assert_direct_cell(&state_a, scalar_cell, &first_values[0]);
    assert_direct_cell(&state_a, point_cell, &first_values[1]);
    assert_map_cell(&state_a, scalar_map, &owner7, &first_values[0]);
    assert_map_cell(&state_a, point_map, &domain_a_key, &first_values[1]);
    assert_tree_cell(&state_a, scalars, &owner7, &domain_a_key, &first_values[0]);
    assert_tree_cell(&state_a, points, &domain_a_key, &owner7, &first_values[1]);
    assert_map_size(&state_a, scalar_map, 1);
    assert_map_size(&state_a, point_map, 1);
    assert_tree_sizes(&state_a, scalars, &owner7, 1, 1);
    assert_tree_sizes(&state_a, points, &domain_a_key, 1, 1);

    let second_values = values(5, identity());
    let before_second = state_a.clone();
    let second = prepare(
        &plan,
        &inputs(7, &domain_a, &second_values),
        &state_a,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    assert_eq!(state_a, before_second);
    assert_eq!(
        second.returns_json(),
        expected_returns(
            [&first_values[0], &first_values[1]],
            [&first_values[0], &first_values[1]],
            [&first_values[0], &first_values[1]],
            [&second_values[0], &second_values[1]],
        )
    );
    assert_eq!(check(&second, &circuit).unwrap(), second.activity_schedule);
    let state_a = second.after.state.clone();
    assert_direct_cell(&state_a, scalar_cell, &second_values[0]);
    assert_direct_cell(&state_a, point_cell, &second_values[1]);
    assert_map_cell(&state_a, scalar_map, &owner7, &second_values[0]);
    assert_map_cell(&state_a, point_map, &domain_a_key, &second_values[1]);
    assert_tree_cell(&state_a, scalars, &owner7, &domain_a_key, &second_values[0]);
    assert_tree_cell(&state_a, points, &domain_a_key, &owner7, &second_values[1]);
    assert_map_size(&state_a, scalar_map, 1);
    assert_map_size(&state_a, point_map, 1);
    assert_tree_sizes(&state_a, scalars, &owner7, 1, 1);
    assert_tree_sizes(&state_a, points, &domain_a_key, 1, 1);

    let third_values = values(7, doubled_generator());
    let before_third = state_a.clone();
    let third = prepare(
        &plan,
        &inputs(9, &domain_b, &third_values),
        &state_a,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    assert_eq!(
        third.returns_json(),
        expected_returns(
            [&second_values[0], &second_values[1]],
            [&defaults[0], &defaults[1]],
            [&defaults[0], &defaults[1]],
            [&third_values[0], &third_values[1]],
        )
    );
    assert_eq!(check(&third, &circuit).unwrap(), third.activity_schedule);
    assert_eq!(before_third, state_a);
    let state_ab = &third.after.state;
    assert_direct_cell(state_ab, scalar_cell, &third_values[0]);
    assert_direct_cell(state_ab, point_cell, &third_values[1]);
    assert_map_cell(state_ab, scalar_map, &owner7, &second_values[0]);
    assert_map_cell(state_ab, point_map, &domain_a_key, &second_values[1]);
    assert_map_cell(state_ab, scalar_map, &owner9, &third_values[0]);
    assert_map_cell(state_ab, point_map, &domain_b_key, &third_values[1]);
    assert_tree_cell(state_ab, scalars, &owner7, &domain_a_key, &second_values[0]);
    assert_tree_cell(state_ab, scalars, &owner9, &domain_b_key, &third_values[0]);
    assert_tree_cell(state_ab, points, &domain_a_key, &owner7, &second_values[1]);
    assert_tree_cell(state_ab, points, &domain_b_key, &owner9, &third_values[1]);
    assert_map_size(state_ab, scalar_map, 2);
    assert_map_size(state_ab, point_map, 2);
    assert_tree_sizes(state_ab, scalars, &owner7, 2, 1);
    assert_tree_sizes(state_ab, scalars, &owner9, 2, 1);
    assert_tree_sizes(state_ab, points, &domain_a_key, 2, 1);
    assert_tree_sizes(state_ab, points, &domain_b_key, 2, 1);

    let mut wrong_role = plan.clone();
    wrong_role.state[scalar_map].kind["map"][1] = json!("Native");
    assert_rejected(
        &wrong_role,
        &circuit,
        &state_a,
        7,
        &domain_a,
        &second_values,
    );

    let bad_width = replace_cell(&state_a, scalar_cell, &[Fr::from(1u64), Fr::from(2u64)]);
    assert_rejected(&plan, &circuit, &bad_width, 7, &domain_a, &second_values);

    let scalar_order = canonical_field(JUBJUB_ORDER).unwrap();
    let noncanonical_scalar = replace_cell(&state_a, scalar_cell, &[scalar_order]);
    assert_rejected(
        &plan,
        &circuit,
        &noncanonical_scalar,
        7,
        &domain_a,
        &second_values,
    );

    let order_two_y = Fr::from(0u64) - Fr::from(1u64);
    let order_two_point = replace_cell(&state_a, point_cell, &[Fr::from(0u64), order_two_y]);
    assert_rejected(
        &plan,
        &circuit,
        &order_two_point,
        7,
        &domain_a,
        &second_values,
    );

    assert_rejects_map_key(&plan, "scalarMap", "JubjubScalar");
    assert_rejects_map_key(&plan, "pointMap", "JubjubPoint");
    assert_rejects_tree_key(&plan, "scalars", true, "JubjubScalar");
    assert_rejects_tree_key(&plan, "scalars", false, "JubjubPoint");
    assert_rejects_tree_key(&plan, "points", true, "JubjubPoint");
    assert_rejects_tree_key(&plan, "points", false, "JubjubScalar");
}
