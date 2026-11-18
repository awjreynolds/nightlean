#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Instruction, MODULUS, Plan, check, create_state, field_value, prepare, zkir::IrSource,
};
use num_bigint::BigUint;
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const OLD_PLAN: &str = include_str!(
    "fixtures/generic-state/issue69-bytes32/321/Issue69Bytes32Map.register.impact.json"
);
const OLD_CIRCUIT: &[u8] =
    include_bytes!("fixtures/generic-state/issue69-bytes32/321/Issue69Bytes32Map.register.zkir");
const NEW_PLAN: &str =
    include_str!("fixtures/public-bytes32/321/Issue69Bytes32Map.register.impact.json");
const NEW_CIRCUIT: &[u8] =
    include_bytes!("fixtures/public-bytes32/321/Issue69Bytes32Map.register.zkir");

fn inputs(key: &[u8; 32]) -> BTreeMap<String, Json> {
    let bytes = json!({"kind":"bytes", "values":key.as_slice()});
    BTreeMap::from([("probe".into(), bytes.clone()), ("account".into(), bytes)])
}

fn assert_marker(state: &ChargedState<Db>, key: &[u8; 32], count: usize) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let StateValue::Map(map) = &*array.get(0).expect("map slot exists") else {
        panic!("expected native map")
    };
    assert_eq!(map.size(), count);
    let key: AlignedValue = (*key).into();
    let value = map.get(&key).expect("full bytes key exists");
    let StateValue::Cell(marker) = &*value else {
        panic!("expected marker cell")
    };
    let mut fields = Vec::new();
    marker.value_only_field_repr(&mut fields);
    assert_eq!(fields, vec![Fr::from(1u64)]);
    assert!(map.get(&field_value(Fr::from(0u64))).is_none());
}

fn guarded_lookup_index(plan: &Plan) -> usize {
    plan.operations
        .iter()
        .position(|operation| match operation {
            Instruction::Guarded { operation, .. } => {
                matches!(operation.as_ref(), Instruction::Index { key: Some(_), .. })
            }
            _ => false,
        })
        .expect("source has a guarded byte-key lookup")
}

fn field(bigint: &BigUint) -> Fr {
    Fr::from_le_bytes(&bigint.to_bytes_le()).expect("chunk fits native field")
}

#[test]
fn public_bytes32_packing_matches_bytewise_plan_and_checks_the_two_chunk_frame() {
    let old_json: Json = serde_json::from_str(OLD_PLAN).unwrap();
    let new_json: Json = serde_json::from_str(NEW_PLAN).unwrap();
    assert_eq!(old_json["state"], new_json["state"]);
    assert_eq!(old_json["circuit"]["inputs"], new_json["circuit"]["inputs"]);
    let old_plan: Plan = serde_json::from_value(old_json).unwrap();
    let new_plan: Plan = serde_json::from_value(new_json).unwrap();
    let old_circuit = IrSource::load(OLD_CIRCUIT).unwrap();
    let new_circuit = IrSource::load(NEW_CIRCUIT).unwrap();
    assert_eq!(old_plan.operations.len(), new_plan.operations.len() + 62);
    assert_eq!(old_plan.reads.len(), new_plan.reads.len() + 31);
    assert!(matches!(
        new_plan.operations.first(),
        Some(Instruction::Push {
            storage: false,
            alignment,
            ..
        }) if alignment == "bytes32"
    ));
    assert!(matches!(
        new_plan.operations.get(1),
        Some(Instruction::Popeq { alignment, .. }) if alignment == "bytes32"
    ));

    let state_config = BTreeMap::from([("registered".into(), json!([]))]);
    let mut old_state = create_state(&old_plan, &state_config).unwrap();
    let mut new_state = create_state(&new_plan, &state_config).unwrap();
    assert_eq!(old_state, new_state);
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let zero = [0u8; 32];
    let modulus: [u8; 32] = BigUint::parse_bytes(MODULUS.as_bytes(), 10)
        .unwrap()
        .to_bytes_le()
        .try_into()
        .unwrap();
    let full = [u8::MAX; 32];
    let mut inserted: Vec<&[u8; 32]> = Vec::new();
    let old_guard = guarded_lookup_index(&old_plan);
    let new_guard = guarded_lookup_index(&new_plan);

    for (key, expected_count) in [(&zero, 1), (&modulus, 2), (&full, 3), (&modulus, 3)] {
        let input = inputs(key);
        let old = prepare(&old_plan, &input, &old_state, parameters, address).unwrap();
        let new = prepare(&new_plan, &input, &new_state, parameters, address).unwrap();
        assert_eq!(check(&old, &old_circuit).unwrap(), old.activity_schedule);
        assert_eq!(check(&new, &new_circuit).unwrap(), new.activity_schedule);
        assert_eq!(old.preimage.private_transcript.len(), 32);
        assert_eq!(new.preimage.private_transcript.len(), 32);
        assert_eq!(old.after.state, new.after.state);
        old_state = old.after.state;
        new_state = new.after.state;
        if !inserted.contains(&key) {
            inserted.push(key);
        }
        for inserted_key in &inserted {
            assert_marker(&new_state, inserted_key, expected_count);
        }
        if expected_count == 3 && key == &modulus {
            assert_eq!(old.activity_schedule[old_guard], None);
            assert_eq!(new.activity_schedule[new_guard], None);
        }
    }

    let mut malformed = inputs(&zero);
    malformed.insert("probe".into(), json!({"kind":"bytes","values":vec![0; 31]}));
    assert!(prepare(&new_plan, &malformed, &new_state, parameters, address).is_err());
    malformed.insert(
        "probe".into(),
        json!({"kind":"bytes","values":vec![256; 32]}),
    );
    assert!(prepare(&new_plan, &malformed, &new_state, parameters, address).is_err());

    // The prologue carries FAB fields in high-byte, then low-31-byte order.
    let mut full_key = prepare(&new_plan, &inputs(&full), &new_state, parameters, address).unwrap();
    check(&full_key, &new_circuit).unwrap();
    let low = (BigUint::from(1u8) << 248) - BigUint::from(1u8);
    let high_value = Fr::from(u8::MAX as u64);
    let low_value = field(&low);
    let high_index = full_key
        .preimage
        .public_transcript_inputs
        .iter()
        .position(|value| *value == high_value)
        .expect("public Bytes32 high-byte field is present");
    let low_index = full_key
        .preimage
        .public_transcript_inputs
        .iter()
        .position(|value| *value == low_value)
        .expect("public Bytes32 low-31-byte field is present");
    assert!(high_index < low_index);

    full_key.preimage.public_transcript_inputs[high_index] = Fr::from(256u64);
    assert!(check(&full_key, &new_circuit).is_err());
    full_key.preimage.public_transcript_inputs[high_index] = high_value;
    full_key.preimage.public_transcript_inputs[low_index] = field(&(BigUint::from(1u8) << 248));
    assert!(check(&full_key, &new_circuit).is_err());
    full_key.preimage.public_transcript_inputs[low_index] = low_value;
    full_key.preimage.public_transcript_inputs[high_index] = Fr::from(254u64);
    assert!(check(&full_key, &new_circuit).is_err());
    full_key.preimage.public_transcript_inputs[high_index] = high_value;
    full_key
        .preimage
        .public_transcript_inputs
        .swap(high_index, low_index);
    assert!(check(&full_key, &new_circuit).is_err());
}
