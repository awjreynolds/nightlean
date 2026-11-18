mod common;
use noctium_runtime::{Db, Plan, create_state, prepare};
use onchain_runtime::state::ContractState;
use rand::{Rng, rngs::OsRng};
use serde_json::{Value as Json, json};
use serialize::{Serializable, Tagged, tagged_serialize};
use std::{
    collections::BTreeMap,
    fs,
    path::{Path, PathBuf},
    process::{Command, Output},
};

struct Fixture(PathBuf);
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn encoded<T: Serializable + Tagged>(value: &T) -> Vec<u8> {
    let mut bytes = Vec::new();
    tagged_serialize(value, &mut bytes).unwrap();
    bytes
}
fn write(root: &Path, name: &str, bytes: &[u8]) {
    fs::write(root.join(name), bytes).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(root.join(name), fs::Permissions::from_mode(0o600)).unwrap();
    }
}
fn run(root: &Path, state: &str) -> Output {
    Command::new(env!("CARGO_BIN_EXE_noctium-runtime"))
        .arg(root)
        .args(["--check-state"])
        .arg(root.join(state))
        .arg("--expect-rejection")
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .output()
        .unwrap()
}

#[test]
fn supplied_state_checks_distinguish_rejection_from_loading_failures() {
    let root = Fixture(
        std::env::temp_dir().join(format!("noctium-state-test-{}", OsRng.r#gen::<u64>())),
    );
    fs::create_dir(&root.0).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&root.0, fs::Permissions::from_mode(0o700)).unwrap();
    }
    fs::create_dir(root.0.join("zkir")).unwrap();
    let plan_bytes = serde_json::to_vec(&common::unsigned_json()).unwrap();
    let plan: Plan = serde_json::from_slice(&plan_bytes).unwrap();
    let inputs: BTreeMap<String, Json> =
        serde_json::from_value(json!({"left":"255","right":"255","expected":"510"})).unwrap();
    let parameters = &ledger::structure::INITIAL_PARAMETERS;
    let state = create_state(&plan, &BTreeMap::from([("total".into(), json!("0"))])).unwrap();
    let mut initial = ContractState::<Db>::default();
    initial.data = state;
    let execution = prepare(
        &plan,
        &inputs,
        &initial.data,
        parameters,
        Default::default(),
    )
    .unwrap();
    let mut predicted = initial.clone();
    predicted.data = execution.after.state;
    write(&root.0, "source-plan.json", &plan_bytes);
    write(
        &root.0,
        "zkir/apply.zkir",
        include_bytes!("fixtures/unsigned/circuit.zkir"),
    );
    write(&root.0, "ledger.params", &encoded(parameters));
    write(
        &root.0,
        "native-contract.json",
        serde_json::to_vec(&json!({"address":"00".repeat(32)}))
            .unwrap()
            .as_slice(),
    );
    // An unusable configuration state and absent golden files must be irrelevant.
    write(
        &root.0,
        "runtime-config.json",
        serde_json::to_vec(&json!({"inputs":inputs,"state":{"unused":"invalid"}}))
            .unwrap()
            .as_slice(),
    );
    write(&root.0, "supplied-initial.bin", &encoded(&initial));
    write(&root.0, "supplied-after.bin", &encoded(&predicted));
    let rejected = run(&root.0, "supplied-after.bin");
    assert!(rejected.status.success());
    let result: Json = serde_json::from_slice(&rejected.stdout).unwrap();
    assert_eq!(result["rejected"], json!(true));
    assert_eq!(result["stateUnchangedOnRejection"], json!(true));
    for state in ["supplied-initial.bin", "missing.bin"] {
        let output = run(&root.0, state);
        assert!(!output.status.success());
        assert!(output.stdout.is_empty());
    }
    write(&root.0, "malformed.bin", b"invalid");
    let mut trailing = encoded(&predicted);
    trailing.extend_from_slice(b"trailing");
    write(&root.0, "trailing.bin", &trailing);
    for state in ["malformed.bin", "trailing.bin"] {
        let output = run(&root.0, state);
        assert!(!output.status.success());
        assert!(output.stdout.is_empty());
    }
    write(
        &root.0,
        "runtime-config.json",
        serde_json::to_vec(
            &json!({"inputs":{"left":"bad","right":"255","expected":"510"},"state":{}}),
        )
        .unwrap()
        .as_slice(),
    );
    let output = run(&root.0, "supplied-after.bin");
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    write(
        &root.0,
        "runtime-config.json",
        br#"{"inputs":"SENTINEL_SECRET_PRIVATE_CONFIG","state":{}}"#,
    );
    let output = run(&root.0, "supplied-after.bin");
    assert!(!output.status.success());
    assert!(output.stdout.is_empty());
    let stderr = String::from_utf8(output.stderr).unwrap();
    assert!(stderr.contains("invalid private configuration"));
    assert!(!stderr.contains("SENTINEL_SECRET_PRIVATE_CONFIG"));
}
