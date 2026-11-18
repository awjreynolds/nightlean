//! Real-key qualification, opt in with the three NOCTIUM_TEST_* fixture paths/digest.
use noctium_runtime::{
    artifacts::{self, Role},
    assembly,
};
use rand::{Rng, rngs::OsRng};
use serde_json::Value as Json;
use std::{
    fs,
    path::{Path, PathBuf},
    process::Command,
};

struct Directory(PathBuf);
impl Drop for Directory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}
fn copy(source: &Path, destination: &Path) {
    fs::create_dir(destination).unwrap();
    for item in fs::read_dir(source).unwrap() {
        let item = item.unwrap();
        let kind = item.file_type().unwrap();
        assert!(!kind.is_symlink());
        if kind.is_dir() {
            copy(&item.path(), &destination.join(item.file_name()));
        } else {
            fs::copy(item.path(), destination.join(item.file_name())).unwrap();
        }
    }
}
fn cli(bundle: &Path, digest: &str, config: &Path, output: &Path) -> std::process::Output {
    Command::new(env!("CARGO_BIN_EXE_noctium-assemble"))
        .arg("--bundle")
        .arg(bundle)
        .args(["--manifest-sha256", digest, "--config"])
        .arg(config)
        .args(["--ttl-unix", "2000000000"])
        .arg(output)
        .env_clear()
        .env("PATH", "/usr/bin:/bin")
        .output()
        .unwrap()
}

#[test]
#[ignore = "requires pinned real-key bundle and separate private qualification config"]
fn verified_assembly_authenticates_before_private_access_and_keeps_verified_bytes() {
    let source =
        PathBuf::from(std::env::var_os("NOCTIUM_TEST_BUNDLE").expect("NOCTIUM_TEST_BUNDLE"));
    let digest =
        std::env::var("NOCTIUM_TEST_MANIFEST_SHA256").expect("NOCTIUM_TEST_MANIFEST_SHA256");
    let config_path = PathBuf::from(
        std::env::var_os("NOCTIUM_TEST_PRIVATE_CONFIG").expect("NOCTIUM_TEST_PRIVATE_CONFIG"),
    );
    let mut root = Directory(std::env::temp_dir().join(format!(
        "noctium-verified-assembly-{}",
        OsRng.r#gen::<u64>()
    )));
    fs::create_dir(&root.0).unwrap();
    root.0 = fs::canonicalize(&root.0).unwrap();
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        fs::set_permissions(&root.0, fs::Permissions::from_mode(0o700)).unwrap();
    }
    let bundle_path = root.0.join("bundle");
    copy(&source, &bundle_path);
    let config = fs::read(&config_path).unwrap();
    let verified = artifacts::verify(&bundle_path, Some(&digest)).unwrap();
    let accepted_path = root.0.join("accepted");
    let accepted = cli(&bundle_path, &digest, &config_path, &accepted_path);
    assert!(
        accepted.status.success(),
        "{}",
        String::from_utf8_lossy(&accepted.stderr)
    );
    let summary: Json = serde_json::from_slice(&accepted.stdout).unwrap();
    assert_eq!(summary["officialConstructorPreimageChecked"], true);
    assert_eq!(summary["nodeInvoked"], false);
    assert_eq!(
        fs::read(accepted_path.join("source-plan.json")).unwrap(),
        verified.file(Role::Plan).unwrap()
    );
    let missing_private = root.0.join("private-config-must-not-be-opened.json");
    let wrong_digest_output = root.0.join("wrong-digest");
    let wrong = cli(
        &bundle_path,
        &"0".repeat(64),
        &missing_private,
        &wrong_digest_output,
    );
    assert!(!wrong.status.success());
    assert!(wrong.stdout.is_empty());
    assert!(!wrong_digest_output.exists());
    assert!(
        String::from_utf8(wrong.stderr)
            .unwrap()
            .contains("manifest_digest_mismatch")
    );
    for (index, relative) in [
        "plan/entrypoint.impact.json",
        "keys/entrypoint.prover",
        "profile/target.json",
    ]
    .into_iter()
    .enumerate()
    {
        let path = bundle_path.join(relative);
        let original = fs::read(&path).unwrap();
        let mut altered = original.clone();
        altered[0] ^= 1;
        fs::write(&path, &altered).unwrap();
        let rejected_output = root.0.join(format!("tampered-{index}"));
        let rejected = cli(&bundle_path, &digest, &missing_private, &rejected_output);
        assert!(!rejected.status.success());
        assert!(rejected.stdout.is_empty());
        assert!(!rejected_output.exists());
        assert!(
            String::from_utf8(rejected.stderr)
                .unwrap()
                .contains("digest_mismatch")
        );
        fs::write(path, original).unwrap();
    }
    // Once verified, no mutable public path is opened again, even if all files disappear.
    fs::remove_dir_all(&bundle_path).unwrap();
    let retained_path = root.0.join("retained");
    let retained =
        assembly::assemble_verified(&verified, &config, 2_000_000_000, &retained_path).unwrap();
    assert_eq!(retained["officialConstructorPreimageChecked"], true);
    assert_eq!(
        retained["predictedStateSha256"],
        summary["predictedStateSha256"]
    );
    for (role, name) in [
        (Role::Plan, "source-plan.json"),
        (Role::Circuit, "zkir/claim.zkir"),
        (Role::ProverKey, "keys/claim.prover"),
        (Role::VerifierKey, "keys/claim.verifier"),
        (Role::LedgerParameters, "ledger.params"),
    ] {
        assert_eq!(
            fs::read(retained_path.join(name)).unwrap(),
            verified.file(role).unwrap()
        );
    }
}
