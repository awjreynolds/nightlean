#![cfg(feature = "zkir-321")]

use base_crypto::fab::{AlignedValue, Alignment, AlignmentAtom, Value as FabValue, ValueAtom};
use noctium_runtime::{
    Db, Plan, check, constructor::construct_state, field_value, prepare, zkir::IrSource,
};
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use storage::arena::Sp;
use transient_crypto::curve::Fr;

const PLAN: &str = include_str!("fixtures/byte-storage/321/BytesStorage.update.impact.json");
const CIRCUIT: &[u8] = include_bytes!("fixtures/byte-storage/321/BytesStorage.update.zkir");
const LENGTHS: [usize; 6] = [0, 1, 31, 32, 33, 1024];
const CELLS: [&str; 4] = ["emptyCell", "oneCell", "narrowCell", "wordCell"];
const LABELS: [&str; 6] = ["Empty", "One", "Narrow", "Word", "Map", "Tree"];

fn bytes(value: &[u8]) -> Json {
    json!({"kind":"bytes", "values":value})
}

fn aligned(value: &[u8]) -> AlignedValue {
    AlignedValue::new(
        FabValue(vec![ValueAtom::from(value)]),
        Alignment::singleton(AlignmentAtom::Bytes {
            length: value.len() as u32,
        }),
    )
    .unwrap()
}

fn payloads(seed: u8) -> Vec<Vec<u8>> {
    LENGTHS
        .iter()
        .map(|length| {
            let mut value: Vec<_> = (0..*length)
                .map(|index| seed.wrapping_add(index as u8))
                .collect();
            // The alignment must preserve logical length after FAB normalizes trailing zeros.
            if value.len() > 1 {
                *value.last_mut().unwrap() = 0;
            }
            value
        })
        .collect()
}

fn inputs(owner: u64, domain: &[u8; 32], values: &[Vec<u8>]) -> BTreeMap<String, Json> {
    let mut inputs = BTreeMap::from([
        ("owner".into(), json!(owner.to_string())),
        ("domain".into(), bytes(domain)),
        ("enabled".into(), json!(true)),
        ("empty0".into(), bytes(&[])),
    ]);
    for (length, value) in LENGTHS[1..].iter().zip(&values[1..]) {
        inputs.insert(format!("payload{length}"), bytes(value));
    }
    inputs
}

fn slot(plan: &Plan, name: &str) -> usize {
    plan.state
        .iter()
        .position(|decl| decl.name == name)
        .unwrap()
}

fn state_at(state: &ChargedState<Db>, slot: usize) -> StateValue<Db> {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    (*array.get(slot).unwrap()).clone()
}

fn assert_cell(cell: &StateValue<Db>, value: &[u8]) {
    let StateValue::Cell(cell) = cell else {
        panic!("expected explicit byte cell")
    };
    assert_eq!(**cell, aligned(value));
}

fn assert_state(
    state: &ChargedState<Db>,
    plan: &Plan,
    owner: u64,
    domain: &[u8; 32],
    values: &[Vec<u8>],
) {
    for (name, value) in CELLS.iter().zip(values) {
        assert_cell(&state_at(state, slot(plan, name)), value);
    }
    assert_leaves(state, plan, owner, domain, values);
}

fn assert_leaves(
    state: &ChargedState<Db>,
    plan: &Plan,
    owner: u64,
    domain: &[u8; 32],
    values: &[Vec<u8>],
) {
    let key = field_value(Fr::from(owner));
    let StateValue::Map(ref map) = state_at(state, slot(plan, "values")) else {
        panic!("expected map")
    };
    assert_cell(&map.get(&key).unwrap(), &values[4]);
    let StateValue::Map(ref outer) = state_at(state, slot(plan, "payloads")) else {
        panic!("expected tree")
    };
    let parent = outer.get(&aligned(domain)).unwrap();
    let StateValue::Map(inner) = &*parent else {
        panic!("expected nested map")
    };
    assert_cell(&inner.get(&key).unwrap(), &values[5]);
}

fn replace_cell(state: &ChargedState<Db>, slot: usize, value: StateValue<Db>) -> ChargedState<Db> {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    ChargedState::new(StateValue::Array(array.insert(slot, value).unwrap()))
}

fn assert_rejected(
    plan: &Plan,
    circuit: &IrSource,
    state: &ChargedState<Db>,
    inputs: &BTreeMap<String, Json>,
) {
    let before = state.clone();
    if let Ok(execution) = prepare(
        plan,
        inputs,
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    ) {
        assert!(check(&execution, circuit).is_err());
    }
    assert_eq!(state, &before);
}

#[test]
fn byte_cells_maps_and_nested_leaves_preserve_exact_lengths() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = construct_state(&plan, &BTreeMap::new()).unwrap();
    assert_cell(&state_at(&initial, slot(&plan, "emptyCell")), &[]);
    let defaults: Vec<Vec<u8>> = LENGTHS.iter().map(|length| vec![0; *length]).collect();
    let domain_a = [0xa1; 32];
    let domain_b = [0xb2; 32];
    let first = payloads(7);
    let second = payloads(93);
    let third = payloads(201);
    let mut state = initial.clone();
    for (owner, domain, previous, current, exists) in [
        (7, &domain_a, &defaults, &first, false),
        (7, &domain_a, &first, &second, true),
        (9, &domain_b, &second, &third, false),
    ] {
        let before = state.clone();
        let supplied = inputs(owner, domain, current);
        let mut execution = prepare(
            &plan,
            &supplied,
            &state,
            &ledger::structure::INITIAL_PARAMETERS,
            coin_structure::contract::ContractAddress::default(),
        )
        .unwrap();
        assert_eq!(
            check(&execution, &circuit).unwrap(),
            execution.activity_schedule
        );
        assert_eq!(execution.preimage.private_transcript.len(), 1122);
        let returns = execution.returns_json();
        let mut expected = BTreeMap::from([
            ("mapWasPresent".into(), json!(exists)),
            ("treeWasPresent".into(), json!(exists)),
        ]);
        for (index, label) in LABELS.iter().enumerate() {
            let old = if index >= 4 && !exists {
                &defaults[index]
            } else {
                &previous[index]
            };
            expected.insert(format!("old{label}"), bytes(old));
            expected.insert(format!("new{label}"), bytes(&current[index]));
        }
        assert_eq!(returns, expected);
        assert_eq!(state, before);
        assert_state(&execution.after.state, &plan, owner, domain, current);
        if owner == 9 {
            assert_leaves(&execution.after.state, &plan, 7, &domain_a, &second);
        }
        let original = execution.preimage.public_transcript_outputs[0];
        execution.preimage.public_transcript_outputs[0] = original + Fr::from(1u64);
        assert!(check(&execution, &circuit).is_err());
        if owner == 7 && !exists {
            // Empty bytes erase their payload, never the assertion evaluated before the write.
            let enabled = plan
                .circuit
                .inputs
                .iter()
                .filter(|input| input.visibility == "private")
                .take_while(|input| input.name != "enabled")
                .map(|input| {
                    noctium_runtime::ScalarType::parse(&input.ty)
                        .unwrap()
                        .bytes_length()
                        .unwrap_or(1)
                })
                .sum::<usize>();
            execution.preimage.public_transcript_outputs[0] = original;
            execution.preimage.private_transcript[enabled] = Fr::from(0u64);
            assert!(check(&execution, &circuit).is_err());
        }
        state = execution.after.state;
    }
    let valid_inputs = inputs(7, &domain_a, &second);
    for (name, length) in [("payload1", 0), ("payload33", 32), ("payload1024", 1025)] {
        let mut invalid = valid_inputs.clone();
        invalid.insert(name.into(), bytes(&vec![0; length]));
        assert_rejected(&plan, &circuit, &state, &invalid);
    }
    let mut disabled = valid_inputs.clone();
    disabled.insert("enabled".into(), json!(false));
    assert_rejected(&plan, &circuit, &state, &disabled);
    let mut invalid_empty = valid_inputs.clone();
    invalid_empty.insert("empty0".into(), bytes(&[0]));
    assert_rejected(&plan, &circuit, &state, &invalid_empty);
    for bad in [StateValue::Null, StateValue::Cell(Sp::new(aligned(&[0])))] {
        assert_rejected(
            &plan,
            &circuit,
            &replace_cell(&state, slot(&plan, "emptyCell"), bad),
            &valid_inputs,
        );
    }
    for bad in [
        aligned(&vec![0; 30]),
        field_value(Fr::from(0u64)),
        AlignedValue {
            value: FabValue(vec![ValueAtom(vec![0; 31])]),
            alignment: Alignment::singleton(AlignmentAtom::Bytes { length: 31 }),
        },
    ] {
        let invalid = replace_cell(
            &state,
            slot(&plan, "narrowCell"),
            StateValue::Cell(Sp::new(bad)),
        );
        assert_rejected(&plan, &circuit, &invalid, &valid_inputs);
    }
    let mut wrong_type = plan.clone();
    wrong_type.state[slot(&plan, "values")].kind["map"][1] = json!("Bytes<32>");
    assert_rejected(&wrong_type, &circuit, &state, &valid_inputs);
    let mut wrong_key = plan.clone();
    wrong_key.state[slot(&plan, "values")].kind["map"][0] = json!("Bytes<33>");
    assert!(construct_state(&wrong_key, &BTreeMap::new()).is_err());
}
