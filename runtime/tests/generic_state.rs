//! Source-backed native state effects and adversarial transcript bindings.
use nightlean_runtime::{
    Db, Expr, Instruction, Plan, check, create_state, field_decimal, field_value, prepare,
    zkir::IrSource,
};
use onchain_runtime::ops::Op;
use onchain_runtime::state::{ChargedState, StateValue};
use serde_json::{Value as Json, json};
use sha2::{Digest, Sha256};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;
use transient_crypto::fab::AlignedValueExt;

#[cfg(feature = "zkir-320")]
const PLAN: &str = include_str!("fixtures/generic-state/320/Issue66MixedState.apply.impact.json");
#[cfg(feature = "zkir-321")]
const PLAN: &str = include_str!("fixtures/generic-state/321/Issue66MixedState.apply.impact.json");
#[cfg(feature = "zkir-320")]
const CIRCUIT: &[u8] = include_bytes!("fixtures/generic-state/320/Issue66MixedState.apply.zkir");
#[cfg(feature = "zkir-321")]
const CIRCUIT: &[u8] = include_bytes!("fixtures/generic-state/321/Issue66MixedState.apply.zkir");
#[cfg(feature = "zkir-320")]
const OUTPUT_PLAN: &str =
    include_str!("fixtures/generic-state/320/Issue66OutputState.apply.impact.json");
#[cfg(feature = "zkir-321")]
const OUTPUT_PLAN: &str =
    include_str!("fixtures/generic-state/321/Issue66OutputState.apply.impact.json");
#[cfg(feature = "zkir-320")]
const OUTPUT_CIRCUIT: &[u8] =
    include_bytes!("fixtures/generic-state/320/Issue66OutputState.apply.zkir");
#[cfg(feature = "zkir-321")]
const OUTPUT_CIRCUIT: &[u8] =
    include_bytes!("fixtures/generic-state/321/Issue66OutputState.apply.zkir");
#[cfg(feature = "zkir-321")]
const MAP_READ_PLAN: &str =
    include_str!("fixtures/generic-state/issue68/321/Issue68MapReads.update.impact.json");
#[cfg(feature = "zkir-321")]
const MAP_READ_CIRCUIT: &[u8] =
    include_bytes!("fixtures/generic-state/issue68/321/Issue68MapReads.update.zkir");

#[cfg(feature = "zkir-320")]
const PROFILE: &str = "320";
#[cfg(feature = "zkir-321")]
const PROFILE: &str = "321";

fn plan() -> Plan {
    serde_json::from_str(PLAN).expect("source-generated Impact plan parses")
}

#[cfg(feature = "zkir-321")]
#[test]
fn source_backed_dynamic_map_value_read_is_checked_and_transcript_bound() {
    let plan: Plan = serde_json::from_str(MAP_READ_PLAN).expect("source-generated map plan parses");
    let inputs = BTreeMap::from([("account".to_owned(), json!("17"))]);
    let initial = create_state(
        &plan,
        &BTreeMap::from([("balances".to_owned(), json!([]))]),
    )
    .expect("source map schema creates native state");
    let execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .expect("dynamic map reads pass the upstream native VM");
    assert!(execution.program.iter().any(|operation| matches!(
        operation,
        Op::Idx { path, .. } if path.len() == 2
    )));
    assert_eq!(
        execution
            .preimage
            .public_transcript_outputs
            .iter()
            .copied()
            .map(field_decimal)
            .collect::<Vec<_>>(),
        ["17", "7", "8"]
    );
    assert_eq!(map_value_decimal(&execution.after.state, 0, 17), "8");
    let circuit = IrSource::load(MAP_READ_CIRCUIT).expect("source ZKIR parses");
    assert_eq!(check(&execution, &circuit).unwrap().len(), execution.program.len());

    let mut dishonest = plan.clone();
    let map_index = dishonest
        .operations
        .iter()
        .position(|operation| matches!(operation, Instruction::Index { key: Some(_), .. }))
        .expect("dynamic map read index exists");
    let Instruction::Popeq { expression, .. } = &mut dishonest.operations[map_index + 1] else {
        panic!("dynamic map index is followed by a read binding")
    };
    *expression = Expr::Constant {
        value: "99".to_owned(),
    };
    assert!(prepare(
        &dishonest,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .is_err());
}

fn source_json() -> Json {
    serde_json::from_str(PLAN).expect("source-generated Impact JSON parses")
}

fn circuit() -> IrSource {
    IrSource::load(CIRCUIT).expect("source-generated ZKIR parses")
}

fn initial_state(plan: &Plan) -> ChargedState<Db> {
    create_state(
        plan,
        &serde_json::from_value(json!({
            "counter":"0", "flag":false, "quota":"3", "untouched":"9",
            "claims":[], "receipts":[]
        }))
        .unwrap(),
    )
    .expect("source schema creates typed native state")
}

fn prepare_source(plan: &Plan, state: &ChargedState<Db>) -> nightlean_runtime::Execution {
    prepare(
        plan,
        &BTreeMap::new(),
        state,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .expect("source operations pass runtime/native preparation")
}

fn cell_decimal(state: &ChargedState<Db>, slot: usize) -> String {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected array state")
    };
    let StateValue::Cell(value) = &*array.get(slot).expect("cell slot exists") else {
        panic!("expected cell slot {slot}")
    };
    let mut fields = Vec::new();
    value.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

fn map_value_decimal(state: &ChargedState<Db>, slot: usize, key: u64) -> String {
    let StateValue::Array(array) = state.get_ref() else {
        panic!("expected array state")
    };
    let StateValue::Map(map) = &*array.get(slot).expect("map slot exists") else {
        panic!("expected map slot {slot}")
    };
    let value = map
        .get(&field_value(Fr::from(key)))
        .unwrap_or_else(|| panic!("missing map key {key}"));
    let StateValue::Cell(value) = &*value else {
        panic!("expected map cell value")
    };
    let mut fields = Vec::new();
    value.value_only_field_repr(&mut fields);
    assert_eq!(fields.len(), 1);
    field_decimal(fields[0])
}

fn assert_checker_rejects_plan_mutation(label: &str, mut changed: Json) {
    let plan: Plan = serde_json::from_value(changed.take()).expect("adversarial plan still parses");
    let initial = initial_state(&plan);
    let execution = prepare_source(&plan, &initial);
    assert!(
        check(&execution, &circuit()).is_err(),
        "native checker accepted {label}"
    );
    println!("native-check rejected {label}; prepare passed");
}

#[test]
fn source_backed_generic_state_passes_native_vm_and_checker() {
    let plan = plan();
    assert_eq!(
        plan.state
            .iter()
            .map(|d| (d.name.as_str(), d.kind.to_string()))
            .collect::<Vec<_>>(),
        [
            ("counter", r#"{"cell":"Native"}"#.to_string()),
            ("flag", r#"{"cell":"Bool"}"#.to_string()),
            ("quota", r#"{"cell":"UIntRange<32>"}"#.to_string()),
            ("untouched", r#"{"cell":"Native"}"#.to_string()),
            ("claims", r#"{"map":["UIntRange<32>","Bool"]}"#.to_string()),
            ("receipts", r#"{"map":["Native","Native"]}"#.to_string()),
        ]
    );
    let initial = initial_state(&plan);
    let before = initial.clone();
    let execution = prepare_source(&plan, &initial);
    assert_eq!(
        check(&execution, &circuit()).unwrap().len(),
        execution.program.len()
    );
    assert_eq!(
        execution
            .preimage
            .public_transcript_outputs
            .iter()
            .copied()
            .map(field_decimal)
            .collect::<Vec<_>>(),
        ["0", "2", "3", "4", "1", "0", "0", "9"]
    );
    assert_eq!(cell_decimal(&execution.after.state, 0), "2");
    assert_eq!(cell_decimal(&execution.after.state, 1), "1");
    assert_eq!(cell_decimal(&execution.after.state, 2), "4");
    assert_eq!(cell_decimal(&execution.after.state, 3), "9");
    assert_eq!(map_value_decimal(&execution.after.state, 4, 3), "1");
    assert_eq!(map_value_decimal(&execution.after.state, 5, 7), "11");
    let StateValue::Array(after) = execution.after.state.get_ref() else {
        panic!("expected array")
    };
    let StateValue::Map(claims) = &*after.get(4).unwrap() else {
        panic!("expected claims map")
    };
    let StateValue::Map(receipts) = &*after.get(5).unwrap() else {
        panic!("expected receipts map")
    };
    assert_eq!(claims.size(), 1);
    assert_eq!(receipts.size(), 1);
    assert_eq!(initial, before);
    println!(
        "positive: native prepare + upstream checker passed; reads=[0,2,3,4,1,0,0,9]; typed cells and both map entries matched"
    );
}

#[test]
fn native_checker_rejects_slot_key_value_order_read_and_guard_mutations() {
    let source = source_json();
    let mut wrong_slot = source.clone();
    wrong_slot["operations"][1]["slot"] = json!(3);
    assert_checker_rejects_plan_mutation("state slot binding", wrong_slot);

    let mut wrong_key = source.clone();
    wrong_key["operations"][26]["expression"]["value"]["value"]["value"] = json!("2");
    assert_checker_rejects_plan_mutation("map key binding", wrong_key);

    let mut wrong_value = source.clone();
    wrong_value["operations"][40]["expression"]["value"] = json!("12");
    assert_checker_rejects_plan_mutation("map value binding", wrong_value);

    let plan = plan();
    let initial = initial_state(&plan);
    let mut reordered = prepare_source(&plan, &initial);
    reordered.preimage.public_transcript_inputs.reverse();
    assert!(
        check(&reordered, &circuit()).is_err(),
        "native checker accepted reordered operation transcript"
    );
    println!("native-check rejected reordered operation transcript");

    let mut changed_read = prepare_source(&plan, &initial);
    changed_read.preimage.public_transcript_outputs[1] = Fr::from(8u64);
    assert!(
        check(&changed_read, &circuit()).is_err(),
        "native checker accepted changed after-write read"
    );
    println!("native-check rejected after-write read binding");

    let mut changed_guard = prepare_source(&plan, &initial);
    changed_guard.preimage.public_transcript_outputs[5] = Fr::from(1u64);
    assert!(
        check(&changed_guard, &circuit()).is_err(),
        "native checker accepted false map-absence guard"
    );
    println!("native-check rejected map-absence guard binding");
}

#[test]
fn generated_zkir_contains_five_bit_uint_read_constraints() {
    let circuit: Json = serde_json::from_slice(CIRCUIT).expect("source-generated ZKIR JSON parses");
    let constrained_five = circuit["instructions"]
        .as_array()
        .unwrap()
        .iter()
        .any(|i| i["op"] == "constrain_bits" && i["bits"] == 5);
    assert!(
        constrained_five,
        "UInt 5 source reads lost their 5-bit native constraints"
    );
    println!("positive: source-generated ZKIR contains constrain_bits=5");
}

#[test]
fn computed_circuit_output_binds_the_write_and_later_read() {
    let plan: Plan = serde_json::from_str(OUTPUT_PLAN).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("counter".into(), json!("0"))])).unwrap();
    let mut execution = prepare(
        &plan,
        &BTreeMap::from([("supplied".into(), json!("4"))]),
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    let circuit = IrSource::load(OUTPUT_CIRCUIT).unwrap();
    check(&execution, &circuit).unwrap();
    assert_eq!(cell_decimal(&execution.after.state, 0), "5");
    assert_eq!(
        execution
            .preimage
            .public_transcript_outputs
            .iter()
            .copied()
            .map(field_decimal)
            .collect::<Vec<_>>(),
        ["4", "5"]
    );
    for index in 0..2 {
        let honest = execution.preimage.public_transcript_outputs[index];
        execution.preimage.public_transcript_outputs[index] = Fr::from(6u64);
        assert!(
            check(&execution, &circuit).is_err(),
            "unchecked output-binding read {index}"
        );
        execution.preimage.public_transcript_outputs[index] = honest;
        check(&execution, &circuit).unwrap();
    }
}

#[test]
fn fixture_bytes_match_source_manifest() {
    let manifest: Json =
        serde_json::from_str(include_str!("fixtures/generic-state/source-manifest.json")).unwrap();
    let source = include_bytes!("../../tests/Issue66GenericState.lean");
    assert_eq!(
        hex::encode(Sha256::digest(source)),
        manifest["sourceSha256"]
    );
    let output_source = include_bytes!("../../tests/Issue66OutputBinding.lean");
    assert_eq!(
        hex::encode(Sha256::digest(output_source)),
        manifest["additionalSources"][0]["sourceSha256"]
    );
    let profile = manifest["profiles"]
        .as_array()
        .unwrap()
        .iter()
        .find(|entry| entry["profile"] == PROFILE)
        .unwrap();
    let files = profile["files"].as_array().unwrap();
    assert_eq!(files.len(), 4);
    for (name, bytes) in [
        ("Issue66MixedState.apply.impact.json", PLAN.as_bytes()),
        ("Issue66MixedState.apply.zkir", CIRCUIT),
        (
            "Issue66OutputState.apply.impact.json",
            OUTPUT_PLAN.as_bytes(),
        ),
        ("Issue66OutputState.apply.zkir", OUTPUT_CIRCUIT),
    ] {
        let entry = files.iter().find(|entry| entry["file"] == name).unwrap();
        assert_eq!(bytes.len() as u64, entry["bytes"].as_u64().unwrap());
        assert_eq!(hex::encode(Sha256::digest(bytes)), entry["sha256"]);
    }
}
