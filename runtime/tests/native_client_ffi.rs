//! Owned-client mailbox/correlation tests require neither a node nor private witnesses.
use nightlean_runtime::native_ffi::*;
use serde_json::{Value, json};
fn descriptor() -> Vec<u8> {
    serde_json::to_vec(&json!({"abiVersion":1,"policy":{"networkId":"undeployed","genesis":"8".repeat(64),"specVersion":2001100,"transactionVersion":4,"profile":nightlean_runtime::profile::NAME,"maxDust":"10000000000000000000000"},"capabilities":{"chain":"chain","funding":"wallet","signing":"signer","journal":"store"}})).unwrap()
}
fn context(id: char) -> Vec<u8> {
    serde_json::to_vec(&json!({"protocolVersion":1,"namespace":"test","baseRevision":"r0","attemptId":id.to_string().repeat(64),"capabilities":[{"id":"store","namespace":"test","keyPrefix":"claims/","operations":["private_state.stage.v1","private_state.compare_exchange.v1"]}],"operations":[],"providers":[],"commitCapability":"store"})).unwrap()
}
unsafe fn take(t: u64) -> Vec<u8> {
    let mut n = 0;
    assert_eq!(unsafe { nightlean_native_result_length(t, &mut n) }, OK);
    let mut bytes = vec![0; n];
    let mut written = 99;
    assert_eq!(
        unsafe { nightlean_native_result_copy(t, bytes.as_mut_ptr(), n, &mut written) },
        OK
    );
    assert_eq!(written, n);
    assert_eq!(nightlean_native_result_free(t), OK);
    bytes
}
unsafe fn status(c: u64) -> Value {
    let mut t = 0;
    assert_eq!(unsafe { nightlean_client_advance(c, &mut t) }, OK);
    serde_json::from_slice(&unsafe { take(t) }).unwrap()
}
fn reply(s: &Value) -> Value {
    json!({"abiVersion":1,"requestId":s["requestId"],"operation":s["operation"],"capability":s["capability"],"schema":s["schema"],"profile":s["profile"]})
}
unsafe fn resume(c: u64, m: &Value, r: u64) -> (i32, u64) {
    let m = serde_json::to_vec(m).unwrap();
    let mut out = 99;
    let code = unsafe { nightlean_client_resume(c, m.as_ptr(), m.len(), r, &mut out) };
    (code, out)
}
#[test]
fn owned_recovery_mailbox_rejects_crossed_stale_lossy_and_unchecked_replies() {
    unsafe {
        let d = descriptor();
        let ca = context('a');
        let cb = context('b');
        let (mut a, mut b) = (0, 0);
        assert_eq!(
            nightlean_client_recover(d.as_ptr(), d.len(), ca.as_ptr(), ca.len(), &mut a),
            OK
        );
        assert_eq!(
            nightlean_client_recover(d.as_ptr(), d.len(), cb.as_ptr(), cb.len(), &mut b),
            OK
        );
        let sa = status(a);
        let sb = status(b);
        assert_eq!(sa["status"], "need_host");
        assert!(sa["requestId"].is_string());
        assert_eq!(status(a), sa);
        assert_ne!(sa["requestId"], sb["requestId"]);
        let (mut qa, mut qb, mut ra, mut rb) = (0, 0, 0, 0);
        assert_eq!(nightlean_client_request(a, &mut qa), OK);
        assert_eq!(nightlean_client_request(b, &mut qb), OK);
        assert_eq!(nightlean_client_service_failure(qa, &mut ra), OK);
        assert_eq!(nightlean_client_service_failure(qb, &mut rb), OK);
        let ma = reply(&sa);
        let mb = reply(&sb);
        assert_eq!(resume(b, &mb, ra), (INVALID_RESPONSE, 0));
        assert_eq!(status(b), sb);
        for key in [
            "abiVersion",
            "requestId",
            "operation",
            "capability",
            "schema",
            "profile",
            "unknown",
        ] {
            let mut wrong = ma.clone();
            wrong[key] = if key == "abiVersion" {
                json!(2)
            } else {
                json!("wrong")
            };
            assert_eq!(resume(a, &wrong, ra), (INVALID_RESPONSE, 0));
            assert_eq!(status(a), sa);
        }
        let mut lossy = ma.clone();
        lossy["requestId"] = json!(sa["requestId"].as_str().unwrap().parse::<u64>().unwrap());
        assert_eq!(resume(a, &lossy, ra), (INVALID_RESPONSE, 0));
        let mut noncanonical = ma.clone();
        noncanonical["requestId"] = json!(format!("0{}", sa["requestId"].as_str().unwrap()));
        assert_eq!(resume(a, &noncanonical, ra), (INVALID_RESPONSE, 0));
        let mut forged = ma.clone();
        forged["receipt"] = json!({"height":"1","accepted":true});
        assert_eq!(resume(a, &forged, ra), (INVALID_RESPONSE, 0));
        assert_eq!(resume(a, &ma, 42), (INVALID_HANDLE, 0));
        assert_eq!(nightlean_client_detach(a), INVALID_STATE);
        let mut out = 99;
        let cancel = b"cancel";
        assert_eq!(
            nightlean_client_command(a, cancel.as_ptr(), cancel.len(), &mut out),
            INVALID_STATE
        );
        assert_eq!(out, 0);
        assert_eq!(status(a), sa);
        let mut p = 0;
        assert_eq!(nightlean_client_private_request(qa, &mut p), OK);
        let mut n = 99;
        assert_eq!(nightlean_native_result_length(p, &mut n), INVALID_HANDLE);
        assert_eq!(n, 0);
        assert_eq!(nightlean_native_private_length(p, &mut n), OK);
        assert_eq!(n, 64);
        let (code, t) = resume(a, &ma, ra);
        assert_eq!(code, OK);
        let done: Value = serde_json::from_slice(&take(t)).unwrap();
        assert_eq!(done["status"], "step_error");
        assert_eq!(done["error"], "nightlean_client_Persistence");
        assert_eq!(nightlean_native_private_length(p, &mut n), INVALID_HANDLE);
        assert_eq!(
            nightlean_client_service_failure(qa, &mut out),
            INVALID_HANDLE
        );
        assert_eq!(resume(a, &ma, ra), (INVALID_STATE, 0));
        let (code, t) = resume(b, &mb, rb);
        assert_eq!(code, OK);
        take(t);
        assert_eq!(nightlean_client_detach(a), OK);
        assert_eq!(nightlean_client_detach(b), OK);
        // Each live owned recovery future occupies a bounded client slot until resolved.
        let mut clients = Vec::new();
        for _ in 0..8 {
            let mut c = 0;
            assert_eq!(
                nightlean_client_recover(d.as_ptr(), d.len(), ca.as_ptr(), ca.len(), &mut c),
                OK
            );
            clients.push(c)
        }
        assert_eq!(
            nightlean_client_recover(d.as_ptr(), d.len(), ca.as_ptr(), ca.len(), &mut out),
            LIMIT
        );
        assert_eq!(out, 0);
        for c in clients {
            let s = status(c);
            let mut q = 0;
            let mut r = 0;
            assert_eq!(nightlean_client_request(c, &mut q), OK);
            assert_eq!(nightlean_client_service_failure(q, &mut r), OK);
            let (code, t) = resume(c, &reply(&s), r);
            assert_eq!(code, OK);
            take(t);
            assert_eq!(nightlean_client_detach(c), OK);
        }
    }
}
