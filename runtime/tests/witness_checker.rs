//! Exercise actual emitted CALL constraints independently of provider and host checks.
use nightlean_runtime::{Plan, check, create_state, prepare, zkir::IrSource};
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

#[cfg(feature = "zkir-320")]
const SCALAR_PLAN: &str =
    include_str!("fixtures/witness/320/TypedWitness.ScalarWitness.claim.impact.json");
#[cfg(feature = "zkir-321")]
const SCALAR_PLAN: &str =
    include_str!("fixtures/witness/321/TypedWitness.ScalarWitness.claim.impact.json");
#[cfg(feature = "zkir-320")]
const PAIR_PLAN: &str =
    include_str!("fixtures/witness/320/TypedWitness.PairWitness.claim.impact.json");
#[cfg(feature = "zkir-321")]
const PAIR_PLAN: &str =
    include_str!("fixtures/witness/321/TypedWitness.PairWitness.claim.impact.json");
#[cfg(feature = "zkir-320")]
const SCALAR_CIRCUIT: &[u8] =
    include_bytes!("fixtures/witness/320/TypedWitness.ScalarWitness.claim.zkir");
#[cfg(feature = "zkir-321")]
const SCALAR_CIRCUIT: &[u8] =
    include_bytes!("fixtures/witness/321/TypedWitness.ScalarWitness.claim.zkir");
#[cfg(feature = "zkir-320")]
const PAIR_CIRCUIT: &[u8] =
    include_bytes!("fixtures/witness/320/TypedWitness.PairWitness.claim.zkir");
#[cfg(feature = "zkir-321")]
const PAIR_CIRCUIT: &[u8] =
    include_bytes!("fixtures/witness/321/TypedWitness.PairWitness.claim.zkir");

fn check_mutations(plan_json: &str, circuit_bytes: &[u8], inputs: Json, mutations: &[(&str, u64)]) {
    let plan: Plan = serde_json::from_str(plan_json).unwrap();
    let inputs: BTreeMap<String, Json> = serde_json::from_value(inputs).unwrap();
    let initial = create_state(&plan, &BTreeMap::from([("total".into(), json!("0"))])).unwrap();
    let mut execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    let circuit = IrSource::load(circuit_bytes).unwrap();
    check(&execution, &circuit).unwrap();
    let private_names: Vec<_> = plan
        .circuit
        .inputs
        .iter()
        .filter(|input| input.visibility == "private")
        .map(|input| input.name.as_str())
        .collect();
    assert_eq!(
        private_names.len(),
        execution.preimage.private_transcript.len()
    );
    for (name, dishonest_value) in mutations {
        let position = private_names
            .iter()
            .position(|input| input == name)
            .unwrap();
        let honest_value = execution.preimage.private_transcript[position];
        execution.preimage.private_transcript[position] = Fr::from(*dishonest_value);
        // The host evaluator and provider validators have already run. Only the
        // upstream native relation checker sees this altered private preimage.
        assert!(
            check(&execution, &circuit).is_err(),
            "unchecked leaf {name}"
        );
        execution.preimage.private_transcript[position] = honest_value;
        check(&execution, &circuit).unwrap();
    }
}

#[test]
fn official_call_checker_rejects_each_dishonest_scalar_witness() {
    check_mutations(
        SCALAR_PLAN,
        SCALAR_CIRCUIT,
        json!({
            "expected":"14", "seed":"7", "$helper3":"1", "$helper6":"1",
            "$helper9":"14", "$helper12":"1", "$helper15":"14"
        }),
        &[
            ("$helper3", 0),
            ("$helper6", 0),
            ("$helper9", 13),
            ("$helper12", 0),
            ("$helper15", 13),
            ("$helper9", 256),
        ],
    );
}

#[test]
fn official_call_checker_rejects_dishonest_nominal_result_and_encodings() {
    check_mutations(
        PAIR_PLAN,
        PAIR_CIRCUIT,
        json!({
            "expected":"14", "request.amount":"7", "request.okay":"1",
            "$helper7":"14", "$helper8":"1"
        }),
        &[
            ("$helper7", 13),
            ("$helper7", 256),
            ("$helper8", 0),
            ("$helper8", 2),
            ("request.amount", 256),
            ("request.okay", 2),
        ],
    );
}
