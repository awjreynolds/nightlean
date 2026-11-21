#![cfg(feature = "zkir-321")]

use base_crypto::{fab::AlignedValue, hash::HashOutput};
use coin_structure::{
    coin::{Info as ShieldedCoinInfo, Nonce, ShieldedTokenType},
    contract::ContractAddress,
    transfer::Recipient,
};
use noctium_runtime::{
    Db, Plan, Program, check, create_state, prepare_with_context, zkir::IrSource,
};
use onchain_runtime::{
    context::QueryContext,
    ops::{Key, Op},
    program_fragments::{Map_insert_coin, kernel_claim_zswap_coin_receive},
    state::{ChargedState, StateValue},
};
use serde_json::{Value as Json, json};
use std::{collections::BTreeMap, env, fs, path::PathBuf};
use storage::arena::Sp;

const UINT128: &str = "UIntRange<340282366920938463463374607431768211456>";
const UINT64: &str = "UIntRange<18446744073709551616>";

fn plan_json() -> Json {
    let mut plan = json!({
        "schemaVersion": 1,
        "entrypoint": "receive",
        "circuit": {
            "inputs": [
                {"name":"nonce", "type":"Bytes<32>", "visibility":"private"},
                {"name":"color", "type":"Bytes<32>", "visibility":"private"},
                {"name":"amount", "type":UINT128, "visibility":"private"},
                {"name":"commitment", "type":"Bytes<32>", "visibility":"private"}
            ],
            "outputs": []
        },
        "state": [{
            "name":"coins",
            "kind":{"tree":{"map":["Bytes<32>", {"composite":{
                "id":"Coin",
                "fields":[
                    {"name":"nonce", "type":"Bytes<32>"},
                    {"name":"color", "type":"Bytes<32>"},
                    {"name":"value", "type":UINT128},
                    {"name":"mtIndex", "type":UINT64}
                ]
            }}]}}
        }],
        "operations": [{
            "op":"receiveShieldedToMap",
            "slot":0,
            "nonce":{"tag":"reference", "name":"nonce"},
            "color":{"tag":"reference", "name":"color"},
            "amount":{"tag":"reference", "name":"amount"},
            "commitment":{"tag":"reference", "name":"commitment"}
        }],
        "reads": []
    });
    plan["target"] = json!(noctium_runtime::profile::NAME);
    plan["targetProfile"] = noctium_runtime::profile::target_json();
    plan
}

fn plan() -> Plan {
    serde_json::from_value(plan_json()).unwrap()
}

fn coin() -> ShieldedCoinInfo {
    ShieldedCoinInfo {
        nonce: Nonce(HashOutput([2; 32])),
        type_: ShieldedTokenType(HashOutput([1; 32])),
        value: 5,
    }
}

fn address() -> ContractAddress {
    ContractAddress(HashOutput([3; 32]))
}

fn commitment(coin: &ShieldedCoinInfo) -> coin_structure::coin::Commitment {
    coin.commitment(&Recipient::Contract(address()))
}

fn inputs(coin: &ShieldedCoinInfo, source_commitment: HashOutput) -> BTreeMap<String, Json> {
    BTreeMap::from([
        (
            "nonce".into(),
            json!({"kind":"bytes", "values":coin.nonce.0.0.as_slice()}),
        ),
        (
            "color".into(),
            json!({"kind":"bytes", "values":coin.type_.0.0.as_slice()}),
        ),
        ("amount".into(), json!(coin.value.to_string())),
        (
            "commitment".into(),
            json!({"kind":"bytes", "values":source_commitment.0.as_slice()}),
        ),
    ])
}

fn compiled_inputs(coin: &ShieldedCoinInfo) -> BTreeMap<String, Json> {
    BTreeMap::from([
        (
            "nonce".into(),
            json!({"kind":"bytes", "values":coin.nonce.0.0.as_slice()}),
        ),
        (
            "color".into(),
            json!({"kind":"bytes", "values":coin.type_.0.0.as_slice()}),
        ),
        ("amount".into(), json!(coin.value.to_string())),
    ])
}

fn initial_state(plan: &Plan) -> ChargedState<Db> {
    create_state(plan, &BTreeMap::from([("coins".into(), json!([]))])).unwrap()
}

// This fixture models the host supplying an already-booked output commitment index.
fn context(
    state: ChargedState<Db>,
    coin_commitment: coin_structure::coin::Commitment,
    index: Option<u64>,
) -> QueryContext<Db> {
    let mut context = QueryContext::new(state, address());
    if let Some(index) = index {
        context.call_context.com_indices = context
            .call_context
            .com_indices
            .insert(coin_commitment, index);
    }
    context
}

fn expected_program(coin: ShieldedCoinInfo) -> Program {
    let recipient = Recipient::Contract(address());
    let commitment = coin.commitment(&recipient);
    let mut program: Program = kernel_claim_zswap_coin_receive!((), (), commitment).into();
    let key = AlignedValue::from(coin.nonce);
    let path = vec![Key::Value(AlignedValue::from(0u8).try_into().unwrap())];
    let mut insert = Map_insert_coin!(
        path,
        false,
        AlignedValue,
        ShieldedCoinInfo,
        key,
        coin,
        recipient
    );
    insert[2] = Op::Dup { n: 5 };
    program.extend(insert);
    program
}

#[test]
fn receive_uses_host_context_index_and_pinned_coin_map_program() {
    let plan = plan();
    let state = initial_state(&plan);
    let coin = coin();
    let commitment = commitment(&coin);
    let input = inputs(&coin, commitment.0);
    let expected_program = expected_program(coin.clone());

    for index in [0, 42] {
        let execution = prepare_with_context(
            &plan,
            &input,
            context(state.clone(), commitment, Some(index)),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .unwrap();

        assert_eq!(execution.program, expected_program);
        assert_eq!(execution.program.len(), 16);
        assert_eq!(execution.activity_schedule, vec![None; 16]);
        assert!(
            execution
                .after
                .effects
                .claimed_shielded_receives
                .iter()
                .any(|entry| **entry == commitment)
        );
        assert_eq!(execution.after.qualify(&coin), Some(coin.qualify(index)));

        let StateValue::Array(slots) = execution.after.state.get_ref() else {
            panic!("expected native state array")
        };
        let StateValue::Map(coins) = slots.get(0).unwrap() else {
            panic!("expected coin Map")
        };
        let key = AlignedValue::from(coin.nonce);
        assert_eq!(
            coins.get(&key).as_deref(),
            Some(&StateValue::Cell(Sp::new(AlignedValue::from(
                coin.qualify(index)
            ))))
        );
    }
}

#[test]
fn receive_rejects_unbooked_mismatched_duplicate_and_bare_coins() {
    let plan = plan();
    let coin = coin();
    let commitment = commitment(&coin);
    let input = inputs(&coin, commitment.0);
    let state = initial_state(&plan);
    let params = &ledger::structure::INITIAL_PARAMETERS;

    assert!(
        prepare_with_context(
            &plan,
            &input,
            context(state.clone(), commitment, None),
            params,
        )
        .is_err()
    );

    assert!(
        prepare_with_context(
            &plan,
            &inputs(&coin, HashOutput([9; 32])),
            context(state.clone(), commitment, Some(0)),
            params,
        )
        .is_err()
    );

    let booked =
        prepare_with_context(&plan, &input, context(state, commitment, Some(0)), params).unwrap();
    assert!(
        prepare_with_context(
            &plan,
            &input,
            context(booked.after.state, commitment, Some(0)),
            params,
        )
        .is_err()
    );

    let mut repeated = plan_json();
    let operation = repeated["operations"][0].clone();
    repeated["operations"] = json!([operation.clone(), operation]);
    let repeated: Plan = serde_json::from_value(repeated).unwrap();
    assert!(
        prepare_with_context(
            &repeated,
            &input,
            context(initial_state(&repeated), commitment, Some(0)),
            params,
        )
        .is_err()
    );

    let mut bare = plan_json();
    bare["operations"][0]
        .as_object_mut()
        .unwrap()
        .remove("commitment");
    assert!(serde_json::from_value::<Plan>(bare).is_err());
}

#[test]
fn receive_rejects_guarded_form_and_wrong_map_schema() {
    let mut guarded = plan_json();
    let operation = guarded["operations"][0].clone();
    guarded["operations"][0] = json!({
        "op":"guarded",
        "guard":{"tag":"bool", "value":true},
        "operation":operation
    });
    let guarded: Plan = serde_json::from_value(guarded).unwrap();
    let coin = coin();
    let commitment = commitment(&coin);
    let input = inputs(&coin, commitment.0);
    let state = initial_state(&plan());
    assert!(
        prepare_with_context(
            &guarded,
            &input,
            context(state.clone(), commitment, Some(0)),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .is_err()
    );

    let mut wrong_schema = plan_json();
    wrong_schema["state"][0]["kind"]["tree"]["map"][0] = json!("Native");
    let wrong_schema: Plan = serde_json::from_value(wrong_schema).unwrap();
    assert!(
        prepare_with_context(
            &wrong_schema,
            &input,
            context(state, commitment, Some(0)),
            &ledger::structure::INITIAL_PARAMETERS,
        )
        .is_err()
    );
}

#[test]
#[ignore = "requires generated ShieldedReceive Lean artifacts"]
fn compiled_lean_receive_plan_passes_runtime_check() -> anyhow::Result<()> {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_SHIELDED_RECEIVE_DIR")
            .expect("set generated outputs in NOCTIUM_SHIELDED_RECEIVE_DIR"),
    );
    let plan: Plan = serde_json::from_reader(fs::File::open(
        directory.join("ShieldedReceive.tip.impact.json"),
    )?)?;
    let circuit = IrSource::load(fs::File::open(directory.join("ShieldedReceive.tip.zkir"))?)?;
    let coin = coin();
    let commitment = commitment(&coin);
    let state = create_state(&plan, &BTreeMap::from([("pot".into(), json!([]))]))?;
    let execution = prepare_with_context(
        &plan,
        &compiled_inputs(&coin),
        context(state, commitment, Some(42)),
        &ledger::structure::INITIAL_PARAMETERS,
    )?;

    assert_eq!(check(&execution, &circuit)?, execution.activity_schedule);
    assert!(execution.activity_schedule.ends_with(&[None; 16]));
    Ok(())
}
