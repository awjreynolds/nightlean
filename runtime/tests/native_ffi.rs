//! Native proof ABI phase A. Real fixtures are supplied by the host, never embedded.
use nightlean_runtime::{native_ffi::*, profile};
use rand::RngCore;
use serde_json::{Value, json};
use std::{fs, ptr};
fn coins() -> [u8; 32] {
    let mut bytes = [0; 32];
    rand::rngs::OsRng.fill_bytes(&mut bytes);
    bytes
}
unsafe fn bytes(token: u64, private: bool) -> Vec<u8> {
    let mut len = 0;
    assert_eq!(
        unsafe {
            if private {
                nightlean_native_private_length(token, &mut len)
            } else {
                nightlean_native_result_length(token, &mut len)
            }
        },
        OK
    );
    let mut out = vec![0; len];
    let mut written = 99;
    assert_eq!(
        unsafe {
            if private {
                nightlean_native_private_copy(token, out.as_mut_ptr(), len, &mut written)
            } else {
                nightlean_native_result_copy(token, out.as_mut_ptr(), len, &mut written)
            }
        },
        OK
    );
    assert_eq!(len, written);
    out
}
fn status(s: u64) -> Value {
    unsafe {
        let mut t = 0;
        assert_eq!(nightlean_native_advance(s, &mut t), OK);
        let v = serde_json::from_slice(&bytes(t, false)).unwrap();
        assert_eq!(nightlean_native_result_free(t), OK);
        v
    }
}
fn reply(request: &Value) -> Value {
    json!({"abiVersion":1,"requestId":request["requestId"],"operation":request["operation"],"capability":request["capability"],"profile":request["profile"]})
}
unsafe fn begin(desc: &Value, private: &[u8], parameters: &[u8]) -> (i32, u64) {
    let d = serde_json::to_vec(desc).unwrap();
    let seed = coins();
    let mut out = 99;
    let code = unsafe {
        nightlean_native_begin(
            d.as_ptr(),
            d.len(),
            private.as_ptr(),
            private.len(),
            parameters.as_ptr(),
            parameters.len(),
            seed.as_ptr(),
            32,
            &mut out,
        )
    };
    (code, out)
}
unsafe fn resume(session: u64, reply: &Value, response: &[u8]) -> (i32, u64) {
    let m = serde_json::to_vec(reply).unwrap();
    let mut t = 99;
    let code = unsafe {
        nightlean_native_resume(
            session,
            m.as_ptr(),
            m.len(),
            response.as_ptr(),
            response.len(),
            &mut t,
        )
    };
    (code, t)
}
#[test]
fn forged_tokens_nulls_and_foreign_token_classes_reject() {
    unsafe {
        let mut token = 99;
        let mut size = 99;
        assert_eq!(
            nightlean_native_begin(
                ptr::null(),
                0,
                ptr::null(),
                0,
                ptr::null(),
                0,
                ptr::null(),
                0,
                &mut token
            ),
            INVALID_ARGUMENT
        );
        assert_eq!(token, 0);
        assert_eq!(nightlean_native_advance(1, &mut token), INVALID_HANDLE);
        assert_eq!(token, 0);
        assert_eq!(
            nightlean_native_advance(1, ptr::null_mut()),
            INVALID_ARGUMENT
        );
        assert_eq!(nightlean_native_result_length(1, &mut size), INVALID_HANDLE);
        assert_eq!(size, 0);
        assert_eq!(
            nightlean_native_private_length(1, &mut size),
            INVALID_HANDLE
        );
        assert_eq!(nightlean_native_cancel(1), INVALID_HANDLE);
        assert_eq!(nightlean_native_free(1), INVALID_HANDLE);
        assert_eq!(nightlean_native_result_free(1), INVALID_HANDLE);
        assert_eq!(nightlean_native_private_free(1), INVALID_HANDLE);
    }
}
#[test]
#[ignore = "requires independently authenticated retained claim bundle, private config and SRS"]
fn real_native_pull_resume_rejects_crossed_duplicate_corrupt_and_cancelled_replies() {
    let private = fs::read(std::env::var("NIGHTLEAN_TEST_PRIVATE_CONFIG").unwrap()).unwrap();
    let parameters = fs::read(std::env::var("NIGHTLEAN_TEST_PROOF_PARAMETERS").unwrap()).unwrap();
    let desc = json!({"abiVersion":1,"profile":profile::NAME,"bundleDirectory":std::env::var("NIGHTLEAN_TEST_BUNDLE").unwrap(),"trustedManifestSha256":std::env::var("NIGHTLEAN_TEST_MANIFEST_SHA256").unwrap(),"proofParametersSha256":std::env::var("NIGHTLEAN_TEST_PROOF_PARAMETERS_SHA256").unwrap(),"k":9,"ttl":2000000000u64,"proofServiceCapability":"host.prover","maxResponseBytes":MAX_BYTES});
    unsafe {
        for field in ["profile", "trustedManifestSha256", "proofParametersSha256"] {
            let mut bad = desc.clone();
            bad[field] = json!("0".repeat(64));
            assert_eq!(begin(&bad, &[], &parameters), (INVALID_ARGUMENT, 0));
        }
        assert_eq!(
            begin(&desc, b"SENTINEL_PRIVATE_VALUE", &parameters),
            (INVALID_ARGUMENT, 0)
        );
        let (code, a) = begin(&desc, &private, &parameters);
        assert_eq!(code, OK);
        let (code, b) = begin(&desc, &private, &parameters);
        assert_eq!(code, OK);
        let req = status(a);
        assert_eq!(status(a), req);
        let other = status(b);
        assert_ne!(req["requestId"], other["requestId"]);
        let mut payload = 0;
        assert_eq!(nightlean_native_private_request(a, &mut payload), OK);
        let mut len = 0;
        assert_eq!(
            nightlean_native_result_length(payload, &mut len),
            INVALID_HANDLE
        );
        let private_payload = bytes(payload, true);
        assert!(private_payload.len() > 400_000 && private_payload.len() < MAX_BYTES);
        let mut extra_private = Vec::new();
        for _ in 0..15 {
            let mut token = 0;
            assert_eq!(nightlean_native_private_request(a, &mut token), OK);
            extra_private.push(token);
        }
        let mut limited = 99;
        assert_eq!(nightlean_native_private_request(a, &mut limited), LIMIT);
        assert_eq!(limited, 0);
        for token in extra_private {
            assert_eq!(nightlean_native_private_free(token), OK);
        }
        let mut extra_results = Vec::new();
        for _ in 0..64 {
            let mut token = 0;
            assert_eq!(nightlean_native_advance(a, &mut token), OK);
            extra_results.push(token);
        }
        assert_eq!(nightlean_native_advance(a, &mut limited), LIMIT);
        assert_eq!(limited, 0);
        for token in extra_results {
            assert_eq!(nightlean_native_result_free(token), OK);
        }
        assert_eq!(status(a), req);
        let mut written = 99;
        let mut small = [7; 1];
        assert_eq!(
            nightlean_native_private_copy(payload, small.as_mut_ptr(), 1, &mut written),
            BUFFER_TOO_SMALL
        );
        assert_eq!(written, 0);
        assert_eq!(small, [7]);
        let seed = coins();
        let mut response_token = 99;
        assert_eq!(
            nightlean_native_local_prove(payload, seed.as_ptr(), 32, &mut response_token),
            OK
        );
        let response = bytes(response_token, false);
        assert_eq!(
            nightlean_native_private_length(response_token, &mut len),
            INVALID_HANDLE
        );
        assert_eq!(nightlean_native_result_free(response_token), OK);
        let mut out = 99;
        assert_eq!(
            nightlean_native_local_prove(payload, seed.as_ptr(), 32, &mut out),
            INVALID_STATE
        );
        assert_eq!(out, 0);
        let m = reply(&req);
        for field in [
            "requestId",
            "operation",
            "capability",
            "profile",
            "abiVersion",
            "unknown",
        ] {
            let mut wrong = m.clone();
            wrong[field] = if field == "requestId" {
                other[field].clone()
            } else if field == "abiVersion" {
                json!(2)
            } else {
                json!("wrong")
            };
            assert_eq!(resume(a, &wrong, &response), (INVALID_RESPONSE, 0));
            assert_eq!(status(a), req);
        }
        assert_eq!(resume(b, &m, &response), (INVALID_RESPONSE, 0));
        assert_eq!(resume(b, &reply(&other), &response), (INVALID_RESPONSE, 0));
        assert_eq!(resume(a, &m, b"malformed"), (INVALID_RESPONSE, 0));
        let mut damaged = response.clone();
        *damaged.last_mut().unwrap() ^= 1;
        assert_eq!(resume(a, &m, &damaged), (INVALID_RESPONSE, 0));
        assert_eq!(resume(a, &m, &vec![0; MAX_BYTES + 1]), (LIMIT, 0));
        assert_eq!(status(a), req);
        let gate = std::sync::Arc::new(std::sync::Barrier::new(3));
        let workers = (0..2)
            .map(|_| {
                let gate = gate.clone();
                let metadata = m.clone();
                let response = response.clone();
                std::thread::spawn(move || {
                    gate.wait();
                    resume(a, &metadata, &response)
                })
            })
            .collect::<Vec<_>>();
        gate.wait();
        let results = workers
            .into_iter()
            .map(|w| w.join().unwrap())
            .collect::<Vec<_>>();
        assert_eq!(results.iter().filter(|(code, _)| *code == OK).count(), 1);
        assert_eq!(
            results
                .iter()
                .filter(|(code, token)| *code == INVALID_STATE && *token == 0)
                .count(),
            1
        );
        let finished = results.into_iter().find(|(code, _)| *code == OK).unwrap().1;
        let complete: Value = serde_json::from_slice(&bytes(finished, false)).unwrap();
        assert_eq!(complete["status"], "proved");
        assert_eq!(complete["funded"], false);
        assert_eq!(complete["submitted"], false);
        let encoded = hex::decode(complete["publicIntentHex"].as_str().unwrap()).unwrap();
        let mut reader = encoded.as_slice();
        let _: nightlean_runtime::proof::PublicProvedNativeIntent =
            serialize::tagged_deserialize(&mut reader).unwrap();
        assert!(reader.is_empty());
        assert_eq!(
            nightlean_runtime::artifacts::digest(&encoded),
            complete["publicIntentSha256"]
        );
        assert_eq!(status(a), complete);
        assert_eq!(resume(a, &m, &response), (INVALID_STATE, 0));
        assert_eq!(nightlean_native_cancel(a), INVALID_STATE);
        assert_eq!(
            nightlean_native_private_length(payload, &mut len),
            INVALID_HANDLE
        );
        assert_eq!(nightlean_native_private_free(payload), INVALID_HANDLE);
        assert_eq!(nightlean_native_result_free(finished), OK);
        assert_eq!(nightlean_native_result_free(finished), INVALID_HANDLE);
        let mut revoked = 0;
        assert_eq!(nightlean_native_private_request(b, &mut revoked), OK);
        assert_eq!(nightlean_native_cancel(b), OK);
        assert_eq!(
            nightlean_native_private_length(revoked, &mut len),
            INVALID_HANDLE
        );
        assert_eq!(resume(b, &reply(&other), &response), (INVALID_STATE, 0));
        assert_eq!(nightlean_native_cancel(b), INVALID_STATE);
        assert_eq!(nightlean_native_free(a), OK);
        assert_eq!(nightlean_native_free(a), INVALID_HANDLE);
        assert_eq!(nightlean_native_free(b), OK);
        let (code, c) = begin(&desc, &private, &parameters);
        assert_eq!(code, OK);
        assert_eq!(nightlean_native_cancel(c), OK);
        assert_eq!(nightlean_native_private_request(c, &mut out), INVALID_STATE);
        assert_eq!(nightlean_native_free(c), OK);
        let (code, c) = begin(&desc, &private, &parameters);
        assert_eq!(code, OK);
        assert_eq!(nightlean_native_private_request(c, &mut out), OK);
        assert_eq!(nightlean_native_private_free(out), OK);
        assert_eq!(nightlean_native_private_free(out), INVALID_HANDLE);
        assert_eq!(nightlean_native_free(c), OK);
        println!(
            "native_ffi_profile={} payload={} response={} attached={} positive_and_adversarial=true",
            profile::NAME,
            private_payload.len(),
            response.len(),
            encoded.len()
        );
    }
}
