use nightlean_runtime::{ffi::*, profile};
use serde_json::{Value as Json, json};
use std::borrow::Cow;
#[cfg(feature = "zkir-321")]
use transient_crypto::proofs::Zkir;
use transient_crypto::proofs::{KeyLocation, ProofPreimage};

#[test]
fn build_profile_and_unlabeled_plan_rules_are_explicit() {
    let expected = if cfg!(feature = "zkir-321") {
        ("3.2.1", "7a51b3385bbf4bce3604df87a7c70867c9ab43c0")
    } else {
        ("3.2.0", "446c7fecc6bd41dab99ebe89ab404e9d077d11a9")
    };
    assert_eq!((profile::RELEASE, profile::REVISION), expected);
    assert_eq!(profile::CLI_BANNER, "midnight-zkir 3.2.0");
    assert_eq!(profile::CRATE_VERSION, "3.2.0");
    assert_eq!(
        profile::validate_plan(None, None),
        !cfg!(feature = "zkir-321")
    );
    let target = profile::target_json();
    assert!(profile::validate_plan(Some(profile::NAME), Some(&target)));
    assert!(!profile::validate_plan(Some("other"), Some(&target)));
    let mut mixed = target.clone();
    mixed["zkir"] = json!(if cfg!(feature = "zkir-321") {
        "3.2.0"
    } else {
        "3.2.1"
    });
    assert!(!profile::validate_plan(Some(profile::NAME), Some(&mixed)));
    if cfg!(feature = "zkir-321") {
        assert_eq!(target["nativeSource"]["revision"], profile::REVISION);
    } else {
        assert!(target.get("nativeSource").is_none());
    }
}
#[test]
fn abi_rejects_the_other_native_build_profile_before_execution() {
    let mut params = Vec::new();
    serialize::tagged_serialize(&ledger::structure::INITIAL_PARAMETERS, &mut params).unwrap();
    let mut plan = json!({"schemaVersion":1,"entrypoint":"profile","circuit":{"inputs":[],"outputs":[]},"state":[],"reads":[],"operations":[]});
    if cfg!(feature = "zkir-321") {
        plan["target"] = json!(profile::NAME);
        plan["targetProfile"] = profile::target_json();
    }
    let mut envelope = json!({"abiVersion":1,"profile":profile::ABI,"plan":plan,"publicInputs":{},"state":{},"ledgerParametersHex":hex::encode(params),"address":"00".repeat(32),"circuit":{"version":{"major":3,"minor":2},"inputs":[],"outputs":[],"instructions":[],"do_communications_commitment":true}});
    let bytes = serde_json::to_vec(&envelope).unwrap();
    let (mut session, mut result) = (0, 0);
    assert_eq!(
        unsafe { nightlean_session_begin(bytes.as_ptr(), bytes.len(), &mut session, &mut result) },
        OK
    );
    assert_eq!(nightlean_result_free(result), OK);
    assert_eq!(nightlean_session_free(session), OK);
    envelope["profile"] = json!(if cfg!(feature = "zkir-321") {
        "midnight-ledger-9-zkir-3.2.0"
    } else {
        "midnight-ledger-9-zkir-3.2.1"
    });
    let bytes = serde_json::to_vec(&envelope).unwrap();
    assert_eq!(
        unsafe { nightlean_session_begin(bytes.as_ptr(), bytes.len(), &mut session, &mut result) },
        INVALID_ARGUMENT
    );
    assert_eq!((session, result), (0, 0));
}
fn preimage(inputs: Vec<transient_crypto::curve::Fr>) -> ProofPreimage {
    ProofPreimage {
        inputs,
        private_transcript: vec![],
        public_transcript_inputs: vec![],
        public_transcript_outputs: vec![],
        binding_input: 42u64.into(),
        communications_commitment: None,
        key_location: KeyLocation(Cow::Borrowed("nightlean/profile-regression")),
    }
}
#[test]
fn boolean_release_semantic_cases_use_the_linked_official_checker() {
    let circuit = nightlean_runtime::zkir::IrSource::load(
        include_bytes!("../../tests/zkir321/boolean-deserialization-contract.zkir").as_slice(),
    )
    .unwrap();
    let cases: Vec<Json> =
        serde_json::from_slice(include_bytes!("../../tests/zkir321/boolean-cases.json")).unwrap();
    for case in cases {
        let inputs = [
            case["byte"].as_str().unwrap(),
            case["flag"].as_str().unwrap(),
            case["result"].as_str().unwrap_or("0"),
        ]
        .into_iter()
        .map(|v| nightlean_runtime::canonical_field(v).unwrap())
        .collect();
        let accepted = preimage(inputs).check(&circuit).is_ok();
        assert_eq!(
            accepted,
            case["accepted"].as_bool().unwrap(),
            "{}",
            case["name"]
        );
    }
}
#[test]
#[cfg(feature = "zkir-321")]
fn selected_321_pin_sizes_intermediate_jubjub_without_old_chip_panic() {
    let circuit = nightlean_runtime::zkir::IrSource::load(
        include_bytes!("../../tests/zkir321/jubjub-intermediate.zkir").as_slice(),
    )
    .unwrap();
    assert_eq!(circuit.k(), 10);
    assert!(
        preimage(vec![7u64.into()])
            .check(&circuit)
            .unwrap()
            .is_empty()
    );
}
