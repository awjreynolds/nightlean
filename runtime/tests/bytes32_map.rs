#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, Expr, Instruction, MODULUS, Plan, check, create_state, environment, evaluate, field_value,
    prepare, zkir::IrSource,
};
use num_bigint::BigUint;
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::{curve::Fr, fab::AlignedValueExt};

const PLAN: &str = include_str!(
    "fixtures/generic-state/issue69-bytes32/321/Issue69Bytes32Map.register.impact.json"
);
const CIRCUIT: &[u8] =
    include_bytes!("fixtures/generic-state/issue69-bytes32/321/Issue69Bytes32Map.register.zkir");

fn inputs(key: &[u8; 32]) -> BTreeMap<String, Json> {
    let bytes = json!({"kind":"bytes", "values":key.as_slice()});
    BTreeMap::from([("probe".into(), bytes.clone()), ("account".into(), bytes)])
}

fn assert_marker(state: &ChargedState<Db>, key: &[u8; 32], count: usize) {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected state array")
    };
    let slot = array.get(0).expect("map slot exists");
    let StateValue::Map(map) = &*slot else {
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

#[test]
fn bytes32_keys_preserve_full_identity_and_ordered_native_reads() {
    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("registered".into(), json!([]))])).unwrap();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let zero = [0u8; 32];
    // These keys coincide after reduction modulo Fr, but remain different byte keys.
    let modulus_bytes = BigUint::parse_bytes(MODULUS.as_bytes(), 10)
        .unwrap()
        .to_bytes_le();
    let modulus: [u8; 32] = modulus_bytes.try_into().unwrap();
    let guarded_index = plan
        .operations
        .iter()
        .position(|operation| match operation {
            Instruction::Guarded { operation, .. } => {
                matches!(operation.as_ref(), Instruction::Index { key: Some(_), .. })
            }
            _ => false,
        })
        .expect("source has a guarded byte-key lookup");

    let first = prepare(&plan, &inputs(&zero), &initial, parameters, address).unwrap();
    assert_eq!(check(&first, &circuit).unwrap(), first.activity_schedule);
    assert_eq!(first.activity_schedule[guarded_index], Some(8));
    assert_marker(&first.after.state, &zero, 1);

    let second = prepare(
        &plan,
        &inputs(&modulus),
        &first.after.state,
        parameters,
        address,
    )
    .unwrap();
    assert_eq!(check(&second, &circuit).unwrap(), second.activity_schedule);
    assert_marker(&second.after.state, &zero, 2);
    assert_marker(&second.after.state, &modulus, 2);

    let mut existing = prepare(
        &plan,
        &inputs(&zero),
        &second.after.state,
        parameters,
        address,
    )
    .unwrap();
    assert_eq!(
        check(&existing, &circuit).unwrap(),
        existing.activity_schedule
    );
    assert_eq!(existing.activity_schedule[guarded_index], None);
    assert_marker(&existing.after.state, &zero, 2);

    let mut malformed = inputs(&zero);
    malformed.insert(
        "account".into(),
        json!({"kind":"bytes","values":vec![0; 31]}),
    );
    assert!(prepare(&plan, &malformed, &initial, parameters, address).is_err());
    malformed.insert(
        "account".into(),
        json!({"kind":"bytes","values":vec![256; 32]}),
    );
    assert!(prepare(&plan, &malformed, &initial, parameters, address).is_err());
    let env = environment(&plan, &inputs(&zero)).unwrap();
    assert!(
        evaluate(
            &Expr::Cast {
                ty: "Native".into(),
                value: Box::new(Expr::Reference {
                    name: "account".into()
                }),
            },
            &env
        )
        .is_err()
    );

    // Bind the circuit to the exact native public byte/transcript fields.
    existing.preimage.public_transcript_inputs[4] = Fr::from(1u64);
    assert!(check(&existing, &circuit).is_err());
}
