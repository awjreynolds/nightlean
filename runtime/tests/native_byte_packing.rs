#![cfg(feature = "zkir-321")]

use noctium_runtime::{Expr, Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;

const PLAN: &str =
    include_str!("fixtures/native-byte-packing/321/NativeBytePacking.pack.impact.json");
const CIRCUIT: &[u8] =
    include_bytes!("fixtures/native-byte-packing/321/NativeBytePacking.pack.zkir");

#[test]
fn typed_byte_packing_preserves_chunk_order_and_committed_results() {
    let source: Json = serde_json::from_slice(CIRCUIT).unwrap();
    let packing_counts: Vec<_> = source["instructions"]
        .as_array()
        .unwrap()
        .iter()
        .filter(|instruction| instruction["op"] == "bytes_into_natives")
        .map(|instruction| instruction["outputs"].as_array().unwrap().len())
        .collect();
    assert_eq!(packing_counts, [1, 1, 2, 2, 3]);

    let plan: Plan = serde_json::from_str(PLAN).unwrap();
    let circuit = IrSource::load(CIRCUIT).unwrap();
    let initial = create_state(&plan, &BTreeMap::new()).unwrap();
    let mut inputs = BTreeMap::from([("empty0".into(), json!({"kind":"bytes","values":[]}))]);
    let mut expected =
        BTreeMap::from([("emptyResult".into(), json!({"kind":"bytes","values":[]}))]);
    for length in [1, 31, 32, 62, 63] {
        let mut bytes: Vec<u8> = (0..length).map(|index| (index * 37 + 19) as u8).collect();
        inputs.insert(format!("b{length}"), json!({"kind":"bytes","values":bytes}));
        bytes.reverse();
        expected.insert(format!("r{length}"), json!({"kind":"bytes","values":bytes}));
    }
    let params = &ledger::structure::INITIAL_PARAMETERS;
    let address = coin_structure::contract::ContractAddress::default();
    let execution = prepare(&plan, &inputs, &initial, params, address).unwrap();
    check(&execution, &circuit).unwrap();
    assert_eq!(execution.returns_json(), expected);

    let mut forged = plan;
    let returned = forged
        .returns
        .iter_mut()
        .find(|output| output.name == "r63")
        .unwrap();
    let mut changed: Vec<u8> = expected["r63"]["values"]
        .as_array()
        .unwrap()
        .iter()
        .map(|value| value.as_u64().unwrap() as u8)
        .collect();
    changed[62] ^= 1;
    returned.expression = Expr::BytesLiteral {
        length: 63,
        values: changed,
    };
    let execution = prepare(&forged, &inputs, &initial, params, address).unwrap();
    assert!(check(&execution, &circuit).is_err());
}
