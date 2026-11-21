#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Expr, Instruction, Plan, Value, check, field_value,
    foreign::{ForeignFamily, ForeignRole, ForeignType, ForeignValue},
    merkle::merkle_tree_at,
    prepare,
    zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, path::PathBuf};
use transient_crypto::curve::Fr;

const BASE: ForeignType = ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Base);
const SCALAR: ForeignType = ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Scalar);
const POINT: ForeignType = ForeignType::new(ForeignFamily::Curve25519, ForeignRole::Point);
const SECP_POINT: ForeignType = ForeignType::new(ForeignFamily::Secp256k1, ForeignRole::Point);

fn artifacts() -> PathBuf {
    std::env::var_os("NOCTIUM_FOREIGN_KEY_ARTIFACTS")
        .map(PathBuf::from)
        .expect("set NOCTIUM_FOREIGN_KEY_ARTIFACTS to fresh compiler outputs")
}

fn foreign_value(ty: ForeignType, round: u8) -> ForeignValue {
    let mut bytes = vec![0; ty.byte_len()];
    if ty == POINT && round == 2 {
        return ForeignValue::zero(ty).unwrap();
    }
    if ty == POINT {
        bytes.fill(0x66);
        bytes[0] = 0x58;
    } else if ty == SECP_POINT && round == 2 {
        return ForeignValue::zero(ty).unwrap();
    } else if ty == SECP_POINT {
        bytes = hex::decode("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
            .unwrap();
    } else {
        bytes[0] = round;
    }
    ForeignValue::from_bytes(ty, &bytes).unwrap()
}

fn aligned_key(value: &ForeignValue) -> AlignedValue {
    let fields: Vec<_> = value
        .encode()
        .unwrap()
        .into_iter()
        .map(field_value)
        .collect();
    AlignedValue::concat(fields.iter())
}

fn inputs(
    owner: u64,
    keys: &[ForeignValue; 4],
    amount: u64,
    leaf: u8,
    removing: bool,
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("owner".into(), json!(owner.to_string())),
        (
            "baseKey".into(),
            Value::Foreign(keys[0].clone()).public_json(),
        ),
        (
            "scalarKey".into(),
            Value::Foreign(keys[1].clone()).public_json(),
        ),
        (
            "pointKey".into(),
            Value::Foreign(keys[2].clone()).public_json(),
        ),
        (
            "secpKey".into(),
            Value::Foreign(keys[3].clone()).public_json(),
        ),
        ("amount".into(), json!(amount.to_string())),
        (
            "leafHash".into(),
            json!({"kind":"bytes", "values":vec![leaf; 32]}),
        ),
        ("removing".into(), json!(removing)),
    ])
}

fn slot(plan: &Plan, name: &str) -> usize {
    plan.state
        .iter()
        .position(|declaration| declaration.name == name)
        .unwrap()
}

fn assert_map_keys(state: &ChargedState<Db>, slot: usize, keys: &[AlignedValue]) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected state slots")
    };
    let StateValue::Map(map) = slots.get(slot).unwrap() else {
        panic!("expected map state")
    };
    assert_eq!(map.size(), keys.len());
    for key in keys {
        assert!(map.get(key).is_some(), "expected key in ledger map");
    }
}

fn assert_nested_map_keys(
    state: &ChargedState<Db>,
    slot: usize,
    owner: &AlignedValue,
    keys: &[AlignedValue],
) {
    let StateValue::Array(slots) = state.get_ref() else {
        panic!("expected state slots")
    };
    let StateValue::Map(outer) = slots.get(slot).unwrap() else {
        panic!("expected outer map")
    };
    let parent = outer.get(owner).expect("outer map key exists");
    let StateValue::Map(map) = &*parent else {
        panic!("expected nested map")
    };
    assert_eq!(outer.size(), 1);
    assert_eq!(map.size(), keys.len());
    for key in keys {
        assert!(map.get(key).is_some(), "expected nested foreign key");
    }
}

#[test]
#[ignore = "requires fresh compiler outputs in NOCTIUM_FOREIGN_KEY_ARTIFACTS"]
fn foreign_keys_work_in_maps_sets_nested_paths_and_merkle_reads() {
    let directory = artifacts();
    let plan: Plan = serde_json::from_slice(
        &std::fs::read(directory.join("ForeignKeys.update.impact.json")).unwrap(),
    )
    .unwrap();
    let circuit = IrSource::load(
        std::fs::read(directory.join("ForeignKeys.update.zkir"))
            .unwrap()
            .as_slice(),
    )
    .unwrap();
    let base_slot = slot(&plan, "baseValues");
    let direct_scalar_slot = slot(&plan, "scalarValues");
    let point_map_slot = slot(&plan, "pointValues");
    let secp_map_slot = slot(&plan, "secpValues");
    let set_slot = slot(&plan, "registeredPoints");
    let scalar_slot = slot(&plan, "nestedScalars");
    let group_slot = slot(&plan, "pointGroups");
    let owner_key = field_value(Fr::from(7u64));
    let first = [
        foreign_value(BASE, 5),
        foreign_value(SCALAR, 3),
        foreign_value(POINT, 2),
        foreign_value(SECP_POINT, 2),
    ];
    let second = [
        foreign_value(BASE, 9),
        foreign_value(SCALAR, 6),
        foreign_value(POINT, 1),
        foreign_value(SECP_POINT, 1),
    ];
    let second_base_key = aligned_key(&second[0]);
    let second_direct_scalar_key = aligned_key(&second[1]);
    let second_point_map_key = aligned_key(&second[2]);
    let second_secp_map_key = aligned_key(&second[3]);
    let second_scalar_key = aligned_key(&second[1]);
    let second_point_key = aligned_key(&second[2]);
    let mut state = noctium_runtime::constructor::construct_state(&plan, &BTreeMap::new()).unwrap();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();

    for (keys, amount, leaf, removing, before, after) in [
        (&first, 10, 0xa1, false, false, true),
        (&second, 20, 0xb2, false, false, true),
        (&first, 30, 0xc3, true, true, false),
    ] {
        let execution = prepare(
            &plan,
            &inputs(7, keys, amount, leaf, removing),
            &state,
            parameters,
            address,
        )
        .unwrap();
        assert_eq!(
            check(&execution, &circuit).unwrap(),
            execution.activity_schedule
        );
        let returns = execution.returns_json();
        assert_eq!(returns["baseExisted"], json!(before));
        assert_eq!(returns["baseExists"], json!(after));
        assert_eq!(returns["scalarMapExisted"], json!(before));
        assert_eq!(returns["scalarMapExists"], json!(after));
        assert_eq!(returns["pointMapExisted"], json!(before));
        assert_eq!(returns["pointMapExists"], json!(after));
        assert_eq!(returns["secpMapExisted"], json!(before));
        assert_eq!(returns["secpMapExists"], json!(after));
        assert_eq!(returns["pointExisted"], json!(before));
        assert_eq!(returns["pointExists"], json!(after));
        assert_eq!(returns["scalarExisted"], json!(before));
        assert_eq!(returns["scalarExists"], json!(after));
        assert_eq!(returns["groupedPointExisted"], json!(before));
        assert_eq!(returns["groupedPointExists"], json!(after));
        assert_eq!(
            returns["baseBeforeValue"],
            json!(if before { "10" } else { "0" })
        );
        assert_eq!(
            returns["baseValue"],
            json!(if after {
                amount.to_string()
            } else {
                "0".into()
            })
        );
        state = execution.after.state;
    }

    assert_map_keys(&state, base_slot, &[second_base_key.clone()]);
    assert_map_keys(&state, direct_scalar_slot, &[second_direct_scalar_key]);
    assert_map_keys(&state, point_map_slot, &[second_point_map_key]);
    assert_map_keys(&state, secp_map_slot, &[second_secp_map_key]);
    assert_map_keys(&state, set_slot, &[second_point_key.clone()]);
    assert_nested_map_keys(
        &state,
        scalar_slot,
        &owner_key,
        &[second_scalar_key.clone()],
    );
    assert_nested_map_keys(&state, group_slot, &owner_key, &[second_point_key.clone()]);

    let first_tree = merkle_tree_at(
        &plan.state,
        &state,
        "claimTrees",
        &[Value::Foreign(first[3].clone())],
    )
    .unwrap();
    let second_tree = merkle_tree_at(
        &plan.state,
        &state,
        "claimTrees",
        &[Value::Foreign(second[3].clone())],
    )
    .unwrap();
    let first_view = first_tree.view().unwrap();
    let second_view = second_tree.view().unwrap();
    assert_eq!(first_view.first_free, 2);
    assert_eq!(second_view.first_free, 1);
    assert_eq!(
        first_tree.prehashed_path(0, [0xa1; 32]).unwrap().root(),
        first_view.root
    );
    assert_eq!(
        second_tree.prehashed_path(0, [0xb2; 32]).unwrap().root(),
        second_view.root
    );
    assert!(
        merkle_tree_at(
            &plan.state,
            &state,
            "claimTrees",
            &[Value::Foreign(first[1].clone())],
        )
        .is_err()
    );

    let mut wrong_key_type = plan.clone();
    let projections = wrong_key_type
        .operations
        .iter_mut()
        .find_map(|instruction| {
            let instruction = match instruction {
                Instruction::Guarded { operation, .. } => operation.as_mut(),
                instruction => instruction,
            };
            match instruction {
                Instruction::PushFields {
                    storage: false,
                    expressions,
                    schema,
                } if schema.as_str() == Some("Secp256k1Base") => Some(expressions),
                _ => None,
            }
        })
        .expect("fixture has a typed Base key push");
    for projection in projections {
        let Expr::ForeignEncodedField { value, .. } = projection else {
            panic!("expected a foreign key projection");
        };
        **value = Expr::Reference {
            name: "scalarKey".into(),
        };
    }
    let error = prepare(
        &wrong_key_type,
        &inputs(7, &first, 10, 0xa1, false),
        &state,
        parameters,
        address,
    )
    .err()
    .expect("equal-width foreign key types must stay distinct");
    assert!(format!("{error:#}").contains("map key type mismatch"));
}
