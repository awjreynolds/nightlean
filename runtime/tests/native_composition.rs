#![cfg(feature = "zkir-321")]

use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use ledger::structure::{INITIAL_PARAMETERS, ProofPreimageVersioned};
use noctium_runtime::{
    Plan,
    assembly::{CheckedNativeCall, assemble_checked_calls},
    check, create_state, prepare,
    zkir::IrSource,
};
use onchain_runtime::{
    context::QueryContext,
    state::{ChargedState, EntryPointBuf},
};
use rand::rngs::OsRng;
use serde_json::{Value as Json, json};
use std::collections::BTreeMap;
use transient_crypto::curve::Fr;

fn caller_fixture() -> (Plan, IrSource) {
    (
        serde_json::from_str(include_str!(
            "fixtures/native-call-claims/321/NativeCallClaims.claim.impact.json"
        ))
        .unwrap(),
        IrSource::load(
            include_bytes!("fixtures/native-call-claims/321/NativeCallClaims.claim.zkir")
                .as_slice(),
        )
        .unwrap(),
    )
}

fn callee_fixture() -> (Plan, IrSource) {
    (
        serde_json::from_str(include_str!(
            "fixtures/native-returns/321/NativeReturns.advance.impact.json"
        ))
        .unwrap(),
        IrSource::load(
            include_bytes!("fixtures/native-returns/321/NativeReturns.advance.zkir").as_slice(),
        )
        .unwrap(),
    )
}

fn bytes32(value: HashOutput) -> Json {
    json!({"kind":"bytes", "values":value.0})
}

fn caller_inputs(
    target: HashOutput,
    entry_hash: HashOutput,
    enabled: bool,
) -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("target".into(), bytes32(target)),
        ("entryHash".into(), bytes32(entry_hash)),
        ("enabled".into(), json!(enabled)),
        ("opening".into(), json!("101")),
        ("argument".into(), json!("3")),
        ("expectedBalance".into(), json!("13")),
        ("expectedCount".into(), json!("1")),
        ("expectedEnabled".into(), json!(false)),
    ])
}

fn callee_inputs() -> BTreeMap<String, Json> {
    BTreeMap::from([
        ("amount".into(), json!("3")),
        ("enabled".into(), json!(false)),
    ])
}

fn checked_call<'a>(
    execution: &'a noctium_runtime::Execution,
    circuit: &'a IrSource,
    state: ChargedState<noctium_runtime::Db>,
    address: ContractAddress,
    entry_point: EntryPointBuf,
    randomness: Fr,
) -> CheckedNativeCall<'a> {
    CheckedNativeCall {
        execution,
        circuit,
        initial_context: QueryContext::new(state, address),
        entry_point,
        communication_commitment_rand: randomness,
    }
}

#[test]
fn native_intent_assembles_a_call_forest_and_rejects_unmatched_claims() {
    let (caller_plan, caller_circuit) = caller_fixture();
    let (callee_plan, callee_circuit) = callee_fixture();
    let caller_address = ContractAddress(HashOutput([7; 32]));
    let callee_address = ContractAddress(HashOutput([42; 32]));
    let caller_state = create_state(
        &caller_plan,
        &BTreeMap::from([("marker".into(), json!("9"))]),
    )
    .unwrap();
    let callee_state = create_state(
        &callee_plan,
        &BTreeMap::from([
            ("balance".into(), json!("10")),
            ("count".into(), json!("0")),
        ]),
    )
    .unwrap();
    let callee_entry = EntryPointBuf::from(b"advance".to_vec());
    let callee_execution = prepare(
        &callee_plan,
        &callee_inputs(),
        &callee_state,
        &INITIAL_PARAMETERS,
        callee_address,
    )
    .unwrap();
    check(&callee_execution, &callee_circuit).unwrap();
    assert_eq!(
        callee_execution.returns_json(),
        BTreeMap::from([
            ("balanceValue".into(), json!("13")),
            ("countValue".into(), json!("1")),
            ("enabledValue".into(), json!(false)),
        ])
    );

    let entry_hash = callee_entry.ep_hash();
    let caller_execution = prepare(
        &caller_plan,
        &caller_inputs(callee_address.0, entry_hash, true),
        &caller_state,
        &INITIAL_PARAMETERS,
        caller_address,
    )
    .unwrap();
    assert_eq!(caller_execution.after.state, caller_state);
    assert_eq!(
        caller_execution.returns_json(),
        BTreeMap::from([("didClaim".into(), json!(true))])
    );
    let callee = || {
        checked_call(
            &callee_execution,
            &callee_circuit,
            callee_state.clone(),
            callee_address,
            callee_entry.clone(),
            Fr::from(101u64),
        )
    };
    let caller = |execution| {
        checked_call(
            execution,
            &caller_circuit,
            caller_state.clone(),
            caller_address,
            EntryPointBuf::from(b"claim".to_vec()),
            Fr::from(53u64),
        )
    };
    let assemble = |calls: &[CheckedNativeCall<'_>]| {
        assemble_checked_calls(calls, &INITIAL_PARAMETERS, 1_800_000_000, &mut OsRng)
    };
    let independent_address = ContractAddress(HashOutput([12; 32]));
    let independent_execution = prepare(
        &callee_plan,
        &callee_inputs(),
        &callee_state,
        &INITIAL_PARAMETERS,
        independent_address,
    )
    .unwrap();
    let independent = || {
        checked_call(
            &independent_execution,
            &callee_circuit,
            callee_state.clone(),
            independent_address,
            callee_entry.clone(),
            Fr::from(102u64),
        )
    };
    let intent = assemble(&[caller(&caller_execution), callee(), independent()]).unwrap();
    let assembled: Vec<_> = intent.calls().collect();
    assert_eq!(
        assembled.iter().map(|c| c.address).collect::<Vec<_>>(),
        [caller_address, callee_address, independent_address]
    );
    let ProofPreimageVersioned::V2(preimage) = &assembled[1].proof else {
        panic!("expected a V2 preimage");
    };
    assert_eq!(preimage.inputs, [Fr::from(3u64)]);
    assert_eq!(
        preimage.key_location.0,
        format!("{}:advance", hex::encode(callee_address.0.0))
    );
    assert!(assembled[0].calls(assembled[1]));
    assert!(!assembled[0].calls(assembled[2]));
    assert!(assemble(&[callee(), caller(&caller_execution)]).is_err());
    assert!(assemble(&[caller(&caller_execution)]).is_err());
    assert!(assemble(&[callee(), callee()]).is_err());

    let wrong_tuple = prepare(
        &caller_plan,
        &caller_inputs(HashOutput([43; 32]), entry_hash, true),
        &caller_state,
        &INITIAL_PARAMETERS,
        caller_address,
    )
    .unwrap();
    assert!(assemble(&[caller(&wrong_tuple), callee()]).is_err());

    let prepare_inactive = || {
        prepare(
            &caller_plan,
            &caller_inputs(callee_address.0, entry_hash, false),
            &caller_state,
            &INITIAL_PARAMETERS,
            caller_address,
        )
        .unwrap()
    };
    let inactive = prepare_inactive();
    check(&inactive, &caller_circuit).unwrap();
    assert!(inactive.after.effects.claimed_contract_calls.is_empty());
    assert_eq!(
        inactive.returns_json(),
        BTreeMap::from([("didClaim".into(), json!(false))])
    );
    assert_eq!(
        inactive
            .activity_schedule
            .iter()
            .filter_map(|skip| *skip)
            .collect::<Vec<_>>(),
        [1, 4, 1, 1, 11, 2, 2, 1, 1]
    );
    assert!(assemble(&[caller(&inactive)]).is_ok());

    let mut forged_inactive = prepare_inactive();
    forged_inactive.after.effects = caller_execution.after.effects.clone();
    let mut forged = caller(&forged_inactive);
    forged.initial_context.effects = caller_execution.after.effects.clone();
    assert!(assemble(&[forged, callee()]).is_err());
}

#[test]
#[ignore = "requires independently pinned caller/callee bundles and their native SRS files"]
fn composed_intent_attaches_both_proofs_against_installed_keys() {
    use base_crypto::time::Timestamp;
    use futures::{executor::block_on, future::pending};
    use ledger::{
        structure::{
            ContractDeploy, LedgerParameters, LedgerState, StandardTransaction, Transaction,
        },
        verify::WellFormedStrictness,
    };
    use noctium_runtime::{
        Db,
        artifacts::{Role, verify},
        proof::{CompositionMaterial, Error, PreparedComposition, TrustedParameters},
    };
    use onchain_runtime::state::{ContractOperation, ContractState};
    use rand::{SeedableRng, rngs::StdRng};
    use std::{env, fs, path::PathBuf};
    use transient_crypto::proofs::{VerifierKey, Zkir};

    let root = PathBuf::from(env::var_os("NOCTIUM_COMPOSITION_BUNDLES").unwrap());
    let caller_bundle = verify(
        &root.join("caller-bundle"),
        Some(&env::var("NOCTIUM_COMPOSITION_CALLER_SHA256").unwrap()),
    )
    .unwrap();
    let callee_bundle = verify(
        &root.join("callee-bundle"),
        Some(&env::var("NOCTIUM_COMPOSITION_CALLEE_SHA256").unwrap()),
    )
    .unwrap();
    let srs = PathBuf::from(env::var_os("NOCTIUM_COMPOSITION_SRS").unwrap());
    let parameters = |circuit: &IrSource, pin: &str| {
        TrustedParameters::from_bytes(
            &fs::read(srs.join(format!("bls_midnight_2p{}", circuit.k()))).unwrap(),
            circuit.k(),
            &env::var(pin).unwrap(),
        )
        .unwrap()
    };

    let deploy = |bundle: &noctium_runtime::artifacts::VerifiedBundle, name: &str, state| {
        let plan = serde_json::from_slice::<Plan>(bundle.file(Role::Plan).unwrap()).unwrap();
        let circuit = IrSource::load(bundle.file(Role::Circuit).unwrap()).unwrap();
        let verifier = serialize::tagged_deserialize::<VerifierKey>(
            &mut bundle.file(Role::VerifierKey).unwrap(),
        )
        .unwrap();
        let entry = EntryPointBuf(name.as_bytes().to_vec());
        let mut contract = ContractState::<Db>::default();
        contract.data = create_state(&plan, &state).unwrap();
        contract.operations = contract
            .operations
            .insert(entry.clone(), ContractOperation::new(Some(verifier), None));
        let deploy = ContractDeploy::new(&mut OsRng, contract);
        (plan, circuit, entry, deploy)
    };
    let (caller_plan, caller_circuit, caller_entry, caller) = deploy(
        &caller_bundle,
        "claim",
        BTreeMap::from([("marker".into(), json!("9"))]),
    );
    let (callee_plan, callee_circuit, callee_entry, callee) = deploy(
        &callee_bundle,
        "advance",
        BTreeMap::from([
            ("balance".into(), json!("10")),
            ("count".into(), json!("0")),
        ]),
    );
    let caller_srs = parameters(&caller_circuit, "NOCTIUM_COMPOSITION_CALLER_SRS_SHA256");
    let callee_srs = parameters(&callee_circuit, "NOCTIUM_COMPOSITION_CALLEE_SRS_SHA256");
    let ledger_parameters = serialize::tagged_deserialize::<LedgerParameters>(
        &mut caller_bundle.file(Role::LedgerParameters).unwrap(),
    )
    .unwrap();
    let mut ledger = LedgerState::<Db>::new("local");
    ledger.parameters = storage::arena::Sp::new(ledger_parameters);
    ledger.contract = ledger
        .contract
        .insert(caller.address(), caller.initial_state.clone())
        .insert(callee.address(), callee.initial_state.clone());
    let before = 1_800_000_000;
    let callee_execution = prepare(
        &callee_plan,
        &callee_inputs(),
        &callee.initial_state.data,
        &ledger.parameters,
        callee.address(),
    )
    .unwrap();
    let caller_execution = prepare(
        &caller_plan,
        &caller_inputs(callee.address().0, callee_entry.ep_hash(), true),
        &caller.initial_state.data,
        &ledger.parameters,
        caller.address(),
    )
    .unwrap();
    let intent = assemble_checked_calls(
        &[
            checked_call(
                &caller_execution,
                &caller_circuit,
                caller.initial_state.data.clone(),
                caller.address(),
                caller_entry,
                Fr::from(53u64),
            ),
            checked_call(
                &callee_execution,
                &callee_circuit,
                callee.initial_state.data.clone(),
                callee.address(),
                callee_entry.clone(),
                Fr::from(101u64),
            ),
        ],
        &ledger.parameters,
        before + 30,
        &mut OsRng,
    )
    .unwrap();
    let selection = [
        CompositionMaterial {
            bundle: &caller_bundle,
            parameters: &caller_srs,
        },
        CompositionMaterial {
            bundle: &callee_bundle,
            parameters: &callee_srs,
        },
    ];
    let mut wrong_ledger = ledger.clone();
    let mut wrong_callee = callee.initial_state.clone();
    let wrong_verifier = serialize::tagged_deserialize::<VerifierKey>(
        &mut caller_bundle.file(Role::VerifierKey).unwrap(),
    )
    .unwrap();
    wrong_callee.operations = wrong_callee.operations.insert(
        callee_entry,
        ContractOperation::new(Some(wrong_verifier), None),
    );
    wrong_ledger.contract = wrong_ledger.contract.insert(callee.address(), wrong_callee);
    assert_eq!(
        PreparedComposition::from_intent(intent.clone(), &wrong_ledger, &selection).err(),
        Some(Error::BindingMismatch)
    );

    let prepared = PreparedComposition::from_intent(intent, &ledger, &selection).unwrap();
    let proved = block_on(prepared.prove_locally(OsRng, pending())).unwrap();
    let tx = Transaction::Standard(StandardTransaction {
        network_id: ledger.network_id.clone(),
        binding_randomness: proved.native().binding_commitment,
        intents: [(1, proved.native().clone())].into_iter().collect(),
        guaranteed_coins: None,
        fallible_coins: Default::default(),
    });
    let mut strictness = WellFormedStrictness::default();
    strictness.enforce_balancing = false;
    tx.seal(StdRng::from_entropy())
        .well_formed(&ledger, strictness, Timestamp::from_secs(before))
        .unwrap();
}
