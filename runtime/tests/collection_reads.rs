#![cfg(feature = "zkir-321")]

use base_crypto::fab::AlignedValue;
use noctium_runtime::{
    Db, artifacts,
    collection_ffi::noctium_ledger_collection_page,
    field_value,
    native_ffi::{
        OK, noctium_native_result_copy, noctium_native_result_free, noctium_native_result_length,
    },
};
use onchain_runtime::state::{ChargedState, ContractState, StateValue};
use serde_json::{Value, json};
use serialize::tagged_serialize;
use storage::{arena::Sp, storage::HashMap};
use transient_crypto::curve::Fr;

struct Snapshot {
    plan: Vec<u8>,
    state: Vec<u8>,
}

impl Snapshot {
    fn new(plan: Value, state: ChargedState<Db>) -> Self {
        let mut contract = ContractState::<Db>::default();
        contract.data = state;
        let mut state_bytes = Vec::new();
        tagged_serialize(&contract, &mut state_bytes).unwrap();
        Self {
            plan: serde_json::to_vec(&plan).unwrap(),
            state: state_bytes,
        }
    }

    fn page(&self, name: &str, offset: usize, limit: usize) -> Value {
        let request = serde_json::to_vec(&json!({
            "abiVersion": 1,
            "planSha256": artifacts::digest(&self.plan),
            "stateSha256": artifacts::digest(&self.state),
            "name": name,
            "keys": [],
            "offset": offset,
            "limit": limit,
        }))
        .unwrap();
        let mut token = 0;
        unsafe {
            assert_eq!(
                noctium_ledger_collection_page(
                    request.as_ptr(),
                    request.len(),
                    self.plan.as_ptr(),
                    self.plan.len(),
                    self.state.as_ptr(),
                    self.state.len(),
                    &mut token,
                ),
                OK
            );
            let mut length = 0;
            assert_eq!(noctium_native_result_length(token, &mut length), OK);
            let mut output = vec![0; length];
            let mut written = 0;
            assert_eq!(
                noctium_native_result_copy(token, output.as_mut_ptr(), length, &mut written),
                OK
            );
            assert_eq!(written, length);
            assert_eq!(noctium_native_result_free(token), OK);
            serde_json::from_slice(&output).unwrap()
        }
    }
}

fn plan(state: Vec<Value>) -> Value {
    let provenance: Value = serde_json::from_str(include_str!(
        "fixtures/issue65/PrivateClaim.claim-321.impact.json"
    ))
    .unwrap();
    json!({
        "schemaVersion": 1,
        "target": provenance["target"],
        "targetProfile": provenance["targetProfile"],
        "state": state,
        "operations": [],
    })
}

fn snapshot() -> Snapshot {
    let map = HashMap::new()
        .insert(
            field_value(Fr::from(10u64)),
            StateValue::Cell(Sp::new(field_value(Fr::from(1u64)))),
        )
        .insert(
            field_value(Fr::from(2u64)),
            StateValue::Cell(Sp::new(field_value(Fr::from(0u64)))),
        )
        .insert(
            field_value(Fr::from(1u64)),
            StateValue::Cell(Sp::new(field_value(Fr::from(1u64)))),
        );
    let set = HashMap::new()
        .insert(AlignedValue::from([9u8; 32]), StateValue::Null)
        .insert(AlignedValue::from([1u8; 32]), StateValue::Null)
        .insert(AlignedValue::from([4u8; 32]), StateValue::Null);
    let state = ChargedState::new(StateValue::Array(
        vec![StateValue::Map(map), StateValue::Map(set)].into(),
    ));
    Snapshot::new(
        plan(vec![
            json!({"name":"flags","kind":{"map":["Native","Bool"]}}),
            json!({"name":"members","kind":{"tree":{"set":"Bytes<32>"}}}),
        ]),
        state,
    )
}

#[test]
fn map_and_set_pages_are_typed_stable_and_bounded() {
    let snapshot = snapshot();

    assert_eq!(
        snapshot.page("flags", 0, 2),
        json!({
            "abiVersion": 1,
            "kind": "map",
            "entries": [
                {"key":"1","value":true},
                {"key":"2","value":false}
            ],
            "nextOffset": 2
        })
    );
    assert_eq!(
        snapshot.page("flags", 2, 2),
        json!({
            "abiVersion": 1,
            "kind": "map",
            "entries": [{"key":"10","value":true}],
            "nextOffset": null
        })
    );

    assert_eq!(
        snapshot.page("members", 0, 2),
        json!({
            "abiVersion": 1,
            "kind": "set",
            "entries": [
                {"kind":"bytes","values":vec![1u8;32]},
                {"kind":"bytes","values":vec![4u8;32]}
            ],
            "nextOffset": 2
        })
    );
    assert_eq!(
        snapshot.page("members", 2, 2),
        json!({
            "abiVersion": 1,
            "kind": "set",
            "entries": [{"kind":"bytes","values":vec![9u8;32]}],
            "nextOffset": null
        })
    );
}
