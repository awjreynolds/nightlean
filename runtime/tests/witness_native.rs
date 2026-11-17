//! Typed source-to-native ABI rejects malformed or stale context handles before allocation.
use nightlean_runtime::native_ffi::{
    INVALID_ARGUMENT, INVALID_HANDLE, nightlean_client_start_from_witness,
    nightlean_native_begin_from_witness, nightlean_native_target_context_free,
    nightlean_native_witness_target_begin,
};
use serde_json::json;

#[test]
fn witness_handoff_abi_is_strict_and_zeroes_failed_outputs() {
    let malformed_target = serde_json::to_vec(&json!({
        "abiVersion": 1,
        "profile": "unexpected",
        "unknown": true
    }))
    .unwrap();
    let state = br#"{"state":{}}"#;
    let mut context = 99;
    let mut result = 99;
    let code = unsafe {
        nightlean_native_witness_target_begin(
            malformed_target.as_ptr(),
            malformed_target.len(),
            state.as_ptr(),
            state.len(),
            std::ptr::null(),
            0,
            std::ptr::null(),
            0,
            &mut context,
            &mut result,
        )
    };
    assert_eq!(code, INVALID_ARGUMENT);
    assert_eq!((context, result), (0, 0));

    let malformed_proof = br#"{"abiVersion":1,"unknown":true}"#;
    let mut proof = 99;
    let code = unsafe {
        nightlean_native_begin_from_witness(
            malformed_proof.as_ptr(),
            malformed_proof.len(),
            u64::MAX,
            u64::MAX,
            std::ptr::null(),
            0,
            std::ptr::null(),
            0,
            &mut proof,
        )
    };
    assert_eq!(code, INVALID_ARGUMENT);
    assert_eq!(proof, 0);

    let malformed_client = b"{}";
    let mut client = 99;
    let code = unsafe {
        nightlean_client_start_from_witness(
            u64::MAX,
            malformed_client.as_ptr(),
            malformed_client.len(),
            &mut client,
        )
    };
    assert_eq!(code, INVALID_ARGUMENT);
    assert_eq!(client, 0);
    assert_eq!(
        nightlean_native_target_context_free(u64::MAX),
        INVALID_HANDLE
    );
}
