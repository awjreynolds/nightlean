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

fn inputs(round: u8) -> BTreeMap<String, Json> {
    let mut inputs = BTreeMap::new();
    for (prefix, family, generator) in [
        (
            "k",
            ForeignFamily::Secp256k1,
            "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798",
        ),
        (
            "r",
            ForeignFamily::Secp256r1,
            "036b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296",
        ),
    ] {
        for (name, role) in [
            ("Base", ForeignRole::Base),
            ("Scalar", ForeignRole::Scalar),
            ("Point", ForeignRole::Point),
        ] {
            let ty = ForeignType::new(family, role);
            let mut bytes = vec![0; ty.byte_len()];
            if round != 0 {
                if role == ForeignRole::Point {
                    if round == 1 {
                        bytes = hex::decode(generator).unwrap();
                    }
                } else {
                    bytes[0] = round * 5;
                }
            }
            inputs.insert(
                format!("{prefix}{name}"),
                Value::Foreign(ForeignValue::from_bytes(ty, &bytes).unwrap()).public_json(),
            );
        }
    }
    inputs
}

fn slot(plan: &Plan, name: &str) -> usize {
    plan.state
        .iter()
        .position(|decl| decl.name == name)
        .unwrap()
}

fn foreign_cell(value: &StateValue<Db>, ty: ForeignType) -> Json {
    let StateValue::Cell(value) = value else {
        panic!("expected a foreign cell")
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

fn replace_cell(state: &ChargedState<Db>, slot: usize, fields: &[Fr]) -> ChargedState<Db> {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let atoms: Vec<_> = fields.iter().copied().map(field_value).collect();
    let cell = StateValue::Cell(Sp::new(AlignedValue::concat(atoms.iter())));
    ChargedState::new(StateValue::Array(array.insert(slot, cell).unwrap()))
}

#[test]
fn foreign_cells_and_map_values_roundtrip_through_native_state() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/foreign-storage/321/ForeignStorage.update.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/foreign-storage/321/ForeignStorage.update.zkir").as_slice(),
    )
    .unwrap();
    let mut state = construct_state(&plan, &BTreeMap::new()).unwrap();
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let map_slot = slot(&plan, "kBaseMap");
    let StateValue::Map(map) = &*array.get(map_slot).unwrap() else {
        panic!("expected map")
    };
    let sibling_key = field_value(Fr::from(999u64));
    let sibling_value = (*array.get(slot(&plan, "kBaseCell")).unwrap()).clone();
    let seeded = StateValue::Map(map.insert(sibling_key.clone(), sibling_value.clone()));
    state = ChargedState::new(StateValue::Array(array.insert(map_slot, seeded).unwrap()));
    let zero_inputs = inputs(0);
    let mut previous = zero_inputs.clone();
    for round in [1, 2] {
        let supplied = inputs(round);
        let before = state.clone();
        let mut execution = prepare(
            &plan,
            &supplied,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        check(&execution, &circuit).unwrap();
        let mut expected = BTreeMap::new();
        let StateValue::Array(after) = execution.after.state.get_ref() else {
            panic!("expected state array")
        };
        for (name, value) in &supplied {
            expected.insert(format!("{name}CellResult"), value.clone());
            expected.insert(format!("{name}MapResult"), value.clone());
            let mut capitalized = name.clone();
            capitalized[..1].make_ascii_uppercase();
            expected.insert(format!("old{capitalized}"), previous[name].clone());
            expected.insert(
                format!("missing{capitalized}Map"),
                zero_inputs[name].clone(),
            );
            let ty = ForeignType::parse_source_name(value["type"].as_str().unwrap()).unwrap();
            assert_eq!(
                foreign_cell(&after.get(slot(&plan, &format!("{name}Cell"))).unwrap(), ty),
                *value
            );
            let StateValue::Map(map) = &*after.get(slot(&plan, &format!("{name}Map"))).unwrap()
            else {
                panic!("expected map")
            };
            assert_eq!(map.size(), if name == "kBase" { 2 } else { 1 });
        }
        assert_eq!(execution.returns_json(), expected);
        let StateValue::Map(map) = &*after.get(map_slot).unwrap() else {
            panic!("expected map")
        };
        assert_eq!(*map.get(&sibling_key).unwrap(), sibling_value);
        assert_eq!(state, before);
        let original = execution.preimage.public_transcript_outputs[0];
        execution.preimage.public_transcript_outputs[0] = original + Fr::from(1u64);
        assert!(check(&execution, &circuit).is_err());
        state = execution.after.state.clone();
        previous = supplied;
    }
    for (name, fields) in [
        ("kBaseCell", vec![Fr::from(1u64)]),
        (
            "kBaseCell",
            vec![Fr::from(0u64), Fr::from(u64::MAX) + Fr::from(1u64)],
        ),
        ("kPointCell", vec![Fr::from(0u64); 5]),
    ] {
        let malformed = replace_cell(&state, slot(&plan, name), &fields);
        assert!(
            prepare(
                &plan,
                &inputs(1),
                &malformed,
                &ledger::structure::INITIAL_PARAMETERS,
                coin_structure::contract::ContractAddress::default(),
            )
            .is_err(),
            "noncanonical {name}"
        );
    }
    let mut wrong_schema: Json = serde_json::from_str(include_str!(
        "fixtures/foreign-storage/321/ForeignStorage.update.impact.json"
    ))
    .unwrap();
    let state_schema = wrong_schema["state"].as_array_mut().unwrap();
    state_schema[map_slot]["kind"]["map"][0] = json!("Secp256k1Base");
    let wrong_schema: Plan = serde_json::from_value(wrong_schema).unwrap();
    assert!(construct_state(&wrong_schema, &BTreeMap::new()).is_err());
}
