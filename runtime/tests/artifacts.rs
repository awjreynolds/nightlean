use nightlean_runtime::artifacts::{self, Manifest, Recipe, Role, Selection};
use serde_json::json;
use std::{
    fs,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
};

static NEXT: AtomicU64 = AtomicU64::new(1);
struct Fixture {
    root: PathBuf,
}
impl Fixture {
    fn new() -> Self {
        let root = std::env::temp_dir().join(format!(
            "nightlean-artifact-tests-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        let root = fs::canonicalize(root).unwrap();
        let fixture = Self { root };
        fs::write(fixture.path("Contract.lean"), b"import Nightlean\n").unwrap();
        fs::write(fixture.path("entry.zkir"), json!({"version":{"major":3,"minor":2},"do_communications_commitment":true,"instructions":[]}).to_string()).unwrap();
        let circuit = json!({"name":"relation","file":"relation.zkir","inputs":[],"outputs":[],"constraints":[]});
        fs::write(fixture.path("entry.impact.json"), json!({"schemaVersion":1,"nativeCircuitFile":"Contract.call.zkir","contractName":"Contract","entrypoint":"call","operations":[],"reads":[],"state":[],"circuit":circuit}).to_string()).unwrap();
        let profile = nightlean_runtime::profile::target_json();
        fs::write(fixture.path("target.json"), profile.to_string()).unwrap();
        fs::write(fixture.path("nightlean.json"), json!({"schemaVersion":1,"target":nightlean_runtime::profile::NAME,"targetProfile":profile,"contracts":[{"name":"Contract","state":[],"entrypoints":[{"name":"call","circuit":"relation","nativeCircuitFile":"Contract.call.zkir","nativePlanFile":"Contract.call.impact.json"}]}],"circuits":[circuit]}).to_string()).unwrap();
        fs::write(
            fixture.path("nightlean_runtime.h"),
            b"#define NIGHTLEAN_ABI_VERSION 1u\nint nightlean_session_begin(void);\n",
        )
        .unwrap();
        fs::write(fixture.path("ledger.params"), b"public ledger parameters").unwrap();
        fs::write(fixture.path("entry.prover"), b"synthetic public prover key").unwrap();
        fs::write(
            fixture.path("entry.verifier"),
            b"synthetic public verifier key",
        )
        .unwrap();
        fs::write(fixture.path("tool.json"), json!({"repository":"https://github.com/midnightntwrk/midnight-zkir","revision":"446c7fecc6bd41dab99ebe89ab404e9d077d11a9","rust":"1.100.0","host":"test-host","version":"midnight-zkir 3.2.0","binary":"/private/local/build/zkir","binarySha256":"a".repeat(64),"cargoLockSha256":"b".repeat(64),"command":"cargo +1.100.0 build --release --locked --package midnight-zkir --features binary"}).to_string()).unwrap();
        if cfg!(feature = "zkir-321") {
            let mut plan: serde_json::Value =
                serde_json::from_slice(&fs::read(fixture.path("entry.impact.json")).unwrap())
                    .unwrap();
            plan["target"] = json!(nightlean_runtime::profile::NAME);
            plan["targetProfile"] = profile;
            fs::write(fixture.path("entry.impact.json"), plan.to_string()).unwrap();
            let mut tool: serde_json::Value =
                serde_json::from_slice(&fs::read(fixture.path("tool.json")).unwrap()).unwrap();
            tool["revision"] = json!(nightlean_runtime::profile::REVISION);
            tool["requestedVersion"] = json!(nightlean_runtime::profile::RELEASE);
            tool["releaseLabel"] = json!(nightlean_runtime::profile::RELEASE);
            tool["expectedCliVersion"] = json!(nightlean_runtime::profile::CRATE_VERSION);
            fs::write(fixture.path("tool.json"), tool.to_string()).unwrap();
        }
        fixture
    }
    fn path(&self, name: &str) -> PathBuf {
        self.root.join(name)
    }
    fn recipe(&self) -> Recipe {
        Recipe {
            schema_version: 1,
            compiler_revision: "c".repeat(40),
            files: vec![
                self.selection(Role::Source, "examples/Contract.lean", "Contract.lean"),
                self.selection(Role::Circuit, "Contract.call.zkir", "entry.zkir"),
                self.selection(Role::Plan, "Contract.call.impact.json", "entry.impact.json"),
                self.selection(Role::Metadata, "nightlean.json", "nightlean.json"),
                self.selection(Role::Abi, "nightlean_runtime.h", "nightlean_runtime.h"),
                self.selection(Role::Profile, "target.json", "target.json"),
                self.selection(Role::LedgerParameters, "ledger.params", "ledger.params"),
                self.selection(Role::ProverKey, "entrypoint.prover", "entry.prover"),
                self.selection(Role::VerifierKey, "entrypoint.verifier", "entry.verifier"),
                self.selection(Role::Toolchain, "native-zkir.json", "tool.json"),
            ],
        }
    }
    fn selection(&self, role: Role, name: &str, path: &str) -> Selection {
        Selection {
            role,
            name: name.into(),
            input: self.path(path),
        }
    }
    fn assemble(&self, name: &str) -> Manifest {
        artifacts::assemble(self.recipe(), &self.path(name)).unwrap()
    }
}
impl Drop for Fixture {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}
fn failure<T>(result: artifacts::Result<T>) -> String {
    match result {
        Ok(_) => panic!("expected rejection"),
        Err(error) => error.code.into(),
    }
}
fn rewrite_manifest(root: &Path, manifest: &Manifest) {
    fs::write(
        root.join("manifest.json"),
        artifacts::manifest_bytes(manifest).unwrap(),
    )
    .unwrap();
}

#[test]
fn assembly_is_canonical_order_independent_and_retains_verified_bytes() {
    let fixture = Fixture::new();
    let first = fixture.assemble("first");
    let mut recipe = fixture.recipe();
    recipe.files.reverse();
    let second = artifacts::assemble(recipe, &fixture.path("second")).unwrap();
    assert_eq!(first, second);
    assert_eq!(
        fs::read(fixture.path("first/manifest.json")).unwrap(),
        fs::read(fixture.path("second/manifest.json")).unwrap()
    );
    let bytes = artifacts::manifest_bytes(&first).unwrap();
    assert!(
        !String::from_utf8(bytes.clone())
            .unwrap()
            .contains("/private/")
    );
    let bundle =
        artifacts::verify(&fixture.path("first"), Some(&artifacts::digest(&bytes))).unwrap();
    assert!(
        !String::from_utf8(bundle.file(Role::Toolchain).unwrap().to_vec())
            .unwrap()
            .contains("/private/local")
    );
    fs::write(
        fixture.path("first/source/examples/Contract.lean"),
        "changed later",
    )
    .unwrap();
    assert_eq!(
        bundle.source("examples/Contract.lean").unwrap(),
        b"import Nightlean\n"
    );
    assert_eq!(
        failure(artifacts::assemble(
            fixture.recipe(),
            &fixture.path("first")
        )),
        "destination_exists"
    );
}

#[test]
fn every_payload_role_rejects_same_length_tampering() {
    let fixture = Fixture::new();
    let manifest = fixture.assemble("bundle");
    for entry in &manifest.entries {
        let path = fixture.path("bundle").join(&entry.path);
        let original = fs::read(&path).unwrap();
        let mut changed = original.clone();
        changed[0] ^= 1;
        fs::write(&path, changed).unwrap();
        assert_eq!(
            failure(artifacts::verify(&fixture.path("bundle"), None)),
            "digest_mismatch",
            "{:?}",
            entry.role
        );
        fs::write(path, original).unwrap();
    }
}

#[test]
fn unsupported_profiles_releases_and_plan_associations_reject() {
    let fixture = Fixture::new();
    let original = fs::read(fixture.path("target.json")).unwrap();
    let mut profile: serde_json::Value = serde_json::from_slice(&original).unwrap();
    profile["zkir"] = json!(if cfg!(feature = "zkir-321") {
        "3.2.0"
    } else {
        "3.2.1"
    });
    fs::write(fixture.path("target.json"), profile.to_string()).unwrap();
    assert_eq!(
        failure(artifacts::assemble(
            fixture.recipe(),
            &fixture.path("bad-profile")
        )),
        "profile_mismatch"
    );
    assert!(!fixture.path("bad-profile").exists());
    fs::write(fixture.path("target.json"), original).unwrap();
    let mut plan: serde_json::Value =
        serde_json::from_slice(&fs::read(fixture.path("entry.impact.json")).unwrap()).unwrap();
    plan["nativeCircuitFile"] = json!("Other.call.zkir");
    fs::write(fixture.path("entry.impact.json"), plan.to_string()).unwrap();
    assert_eq!(
        failure(artifacts::assemble(
            fixture.recipe(),
            &fixture.path("bad-plan")
        )),
        "plan_mismatch"
    );
}

#[test]
fn private_material_traversal_duplicate_roles_and_missing_roles_reject() {
    let fixture = Fixture::new();
    let mut recipe = fixture.recipe();
    recipe.files[0].name = "../outside.lean".into();
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("escape"))),
        "unsafe_path"
    );
    let mut recipe = fixture.recipe();
    recipe.files[0].name = "/absolute.lean".into();
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("absolute"))),
        "unsafe_path"
    );
    let mut recipe = fixture.recipe();
    recipe.files[0].name = "directory\\outside.lean".into();
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("backslash"))),
        "unsafe_path"
    );
    for name in [
        "runtime-config.json",
        "claim-witness.json",
        "private-state.json",
        "checker-preimage.json",
    ] {
        fs::write(fixture.path(name), "private").unwrap();
        let mut recipe = fixture.recipe();
        recipe.files[0].input = fixture.path(name);
        assert_eq!(
            failure(artifacts::assemble(recipe, &fixture.path("private"))),
            "private_artifact"
        );
    }
    fs::write(fixture.path("inputs.json"), "private").unwrap();
    let mut recipe = fixture.recipe();
    recipe.files[0].input = fixture.path("inputs.json");
    assert_eq!(
        failure(artifacts::assemble(
            recipe,
            &fixture.path("mislabeled-json")
        )),
        "invalid_role"
    );
    let mut recipe = fixture.recipe();
    recipe
        .files
        .push(fixture.selection(Role::Circuit, "Other.call.zkir", "entry.zkir"));
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("duplicate"))),
        "duplicate_role"
    );
    let mut recipe = fixture.recipe();
    recipe.files.pop();
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("missing"))),
        "missing_role"
    );
    let mut recipe = fixture.recipe();
    recipe.files.push(fixture.selection(
        Role::Source,
        "examples/Contract.lean/Child.lean",
        "Contract.lean",
    ));
    assert_eq!(
        failure(artifacts::assemble(
            recipe,
            &fixture.path("prefix-conflict")
        )),
        "duplicate_path"
    );
    let mut recipe = fixture.recipe();
    recipe
        .files
        .push(fixture.selection(Role::Source, "examples/contract.lean", "Contract.lean"));
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("case-conflict"))),
        "duplicate_path"
    );
}

#[test]
fn shared_directory_prefixes_require_consistent_casing_before_writing() {
    let fixture = Fixture::new();
    for (first, second, destination) in [
        ("Foo/A.lean", "foo/B.lean", "root-case-alias"),
        ("Foo/Bar/A.lean", "Foo/bar/B.lean", "nested-case-alias"),
        ("Source/A.lean", "source/B.lean", "source-case-alias"),
    ] {
        let mut recipe = fixture.recipe();
        recipe.files[0].name = first.into();
        recipe
            .files
            .push(fixture.selection(Role::Source, second, "Contract.lean"));
        assert_eq!(
            failure(artifacts::assemble(recipe, &fixture.path(destination))),
            "duplicate_path"
        );
        assert!(
            !fixture.path(destination).exists(),
            "conflict must reject before creating output"
        );
    }
    let mut recipe = fixture.recipe();
    recipe.files[0].name = "Foo/A.lean".into();
    recipe
        .files
        .push(fixture.selection(Role::Source, "Foo/B.lean", "Contract.lean"));
    artifacts::assemble(recipe, &fixture.path("consistent-prefix")).unwrap();
    assert!(artifacts::verify(&fixture.path("consistent-prefix"), None).is_ok());
}

#[test]
fn unicode_logical_names_reject_before_filesystem_normalization() {
    let fixture = Fixture::new();
    let mut recipe = fixture.recipe();
    recipe.files[0].name = "é/A.lean".into();
    recipe
        .files
        .push(fixture.selection(Role::Source, "e\u{301}/B.lean", "Contract.lean"));
    assert_eq!(
        failure(artifacts::assemble(
            recipe,
            &fixture.path("normalization-alias")
        )),
        "unsupported_name"
    );
    assert!(!fixture.path("normalization-alias").exists());

    // The portable logical label does not restrict physical input names or source contents.
    fs::write(fixture.path("é.lean"), "def café := 1\n").unwrap();
    let mut recipe = fixture.recipe();
    recipe.files[0].input = fixture.path("é.lean");
    artifacts::assemble(recipe, &fixture.path("unicode-input")).unwrap();
    let bundle = artifacts::verify(&fixture.path("unicode-input"), None).unwrap();
    assert_eq!(
        bundle.source("examples/Contract.lean").unwrap(),
        "def café := 1\n".as_bytes()
    );
}

#[test]
fn private_values_in_unknown_plan_fields_and_wrong_native_source_pin_reject() {
    let fixture = Fixture::new();
    let original = fs::read(fixture.path("entry.impact.json")).unwrap();
    let mut plan: serde_json::Value = serde_json::from_slice(&original).unwrap();
    plan["witnessValues"] = json!({"secret":"42"});
    fs::write(fixture.path("entry.impact.json"), plan.to_string()).unwrap();
    assert_eq!(
        failure(artifacts::assemble(
            fixture.recipe(),
            &fixture.path("private-plan")
        )),
        "unsupported_schema"
    );
    fs::write(fixture.path("entry.impact.json"), original).unwrap();
    let mut provenance: serde_json::Value =
        serde_json::from_slice(&fs::read(fixture.path("tool.json")).unwrap()).unwrap();
    provenance["revision"] = json!("0".repeat(40));
    fs::write(fixture.path("tool.json"), provenance.to_string()).unwrap();
    assert_eq!(
        failure(artifacts::assemble(
            fixture.recipe(),
            &fixture.path("wrong-tool")
        )),
        "profile_mismatch"
    );
}

#[test]
fn manifest_versions_unknown_fields_and_noncanonical_encoding_reject() {
    let fixture = Fixture::new();
    let mut manifest = fixture.assemble("bundle");
    manifest.schema_version = 2;
    rewrite_manifest(&fixture.path("bundle"), &manifest);
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle"), None)),
        "unsupported_version"
    );
    manifest.schema_version = 1;
    manifest.entries[0].path = "../Contract.lean".into();
    rewrite_manifest(&fixture.path("bundle"), &manifest);
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle"), None)),
        "unsafe_path"
    );
    let manifest = fixture.assemble("original");
    let mut value = serde_json::to_value(&manifest).unwrap();
    value["unknown"] = json!(true);
    fs::write(fixture.path("original/manifest.json"), value.to_string()).unwrap();
    assert_eq!(
        failure(artifacts::verify(&fixture.path("original"), None)),
        "invalid_manifest"
    );
    fs::write(
        fixture.path("original/manifest.json"),
        serde_json::to_vec_pretty(&manifest).unwrap(),
    )
    .unwrap();
    assert_eq!(
        failure(artifacts::verify(&fixture.path("original"), None)),
        "noncanonical_manifest"
    );
}

#[test]
fn unsigned_manifest_replacement_needs_external_digest_to_authenticate() {
    let fixture = Fixture::new();
    let mut manifest = fixture.assemble("bundle");
    let expected = artifacts::digest(&artifacts::manifest_bytes(&manifest).unwrap());
    let source = manifest
        .entries
        .iter_mut()
        .find(|entry| entry.role == Role::Source)
        .unwrap();
    let new = b"altered source\n";
    fs::write(fixture.path("bundle").join(&source.path), new).unwrap();
    source.size = new.len() as u64;
    source.sha256 = artifacts::digest(new);
    rewrite_manifest(&fixture.path("bundle"), &manifest);
    assert!(artifacts::verify(&fixture.path("bundle"), None).is_ok());
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle"), Some(&expected))),
        "manifest_digest_mismatch"
    );
}

#[test]
fn unlisted_and_missing_files_reject() {
    let fixture = Fixture::new();
    fixture.assemble("bundle");
    fs::write(fixture.path("bundle/witness.json"), "secret").unwrap();
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle"), None)),
        "unexpected_file"
    );
    fs::remove_file(fixture.path("bundle/witness.json")).unwrap();
    fs::remove_file(fixture.path("bundle/keys/entrypoint.verifier")).unwrap();
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle"), None)),
        "io_error"
    );
}

#[cfg(unix)]
#[test]
fn symlinks_in_sources_payloads_or_bundle_roots_reject() {
    use std::os::unix::fs::symlink;
    let fixture = Fixture::new();
    symlink(fixture.path("Contract.lean"), fixture.path("link.lean")).unwrap();
    let mut recipe = fixture.recipe();
    recipe.files[0].input = fixture.path("link.lean");
    assert_eq!(
        failure(artifacts::assemble(recipe, &fixture.path("source-link"))),
        "unsafe_path"
    );
    fixture.assemble("bundle");
    symlink(fixture.path("bundle"), fixture.path("bundle-link")).unwrap();
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle-link"), None)),
        "unsafe_path"
    );
    fs::remove_file(fixture.path("bundle/source/examples/Contract.lean")).unwrap();
    symlink(
        fixture.path("Contract.lean"),
        fixture.path("bundle/source/examples/Contract.lean"),
    )
    .unwrap();
    assert_eq!(
        failure(artifacts::verify(&fixture.path("bundle"), None)),
        "unsafe_path"
    );
}

#[test]
fn manifest_consumer_rejects_other_linked_native_profile() {
    let fixture = Fixture::new();
    let mut manifest = fixture.assemble("selected");
    assert_eq!(manifest.zkir_revision, nightlean_runtime::profile::REVISION);
    assert_eq!(manifest.profile, nightlean_runtime::profile::NAME);
    manifest.profile = if cfg!(feature = "zkir-321") {
        "midnight-ledger-9"
    } else {
        "midnight-ledger-9-zkir-3.2.1"
    }
    .into();
    manifest.zkir_revision = if cfg!(feature = "zkir-321") {
        "446c7fecc6bd41dab99ebe89ab404e9d077d11a9"
    } else {
        "7a51b3385bbf4bce3604df87a7c70867c9ab43c0"
    }
    .into();
    rewrite_manifest(&fixture.path("selected"), &manifest);
    assert_eq!(
        failure(artifacts::verify(&fixture.path("selected"), None)),
        "profile_mismatch"
    );
}
#[test]
fn tool_release_label_and_source_revision_cannot_be_mixed() {
    let fixture = Fixture::new();
    let original = fs::read(fixture.path("tool.json")).unwrap();
    for (field, value) in [
        (
            "releaseLabel",
            json!(if cfg!(feature = "zkir-321") {
                "3.2.0"
            } else {
                "3.2.1"
            }),
        ),
        ("expectedCliVersion", json!("3.2.1")),
        (
            "revision",
            json!(if cfg!(feature = "zkir-321") {
                "446c7fecc6bd41dab99ebe89ab404e9d077d11a9"
            } else {
                "7a51b3385bbf4bce3604df87a7c70867c9ab43c0"
            }),
        ),
    ] {
        let mut provenance: serde_json::Value = serde_json::from_slice(&original).unwrap();
        provenance[field] = value;
        fs::write(fixture.path("tool.json"), provenance.to_string()).unwrap();
        assert_eq!(
            failure(artifacts::assemble(
                fixture.recipe(),
                &fixture.path("mixed-tool")
            )),
            "profile_mismatch"
        );
        assert!(!fixture.path("mixed-tool").exists());
    }
}

#[test]
fn present_nonstring_plan_target_never_falls_back_to_legacy_profile() {
    let fixture = Fixture::new();
    let original = fs::read(fixture.path("entry.impact.json")).unwrap();
    for target in [
        json!(321),
        json!({"profile":"midnight-ledger-9-zkir-3.2.1"}),
        serde_json::Value::Null,
    ] {
        let mut plan: serde_json::Value = serde_json::from_slice(&original).unwrap();
        plan.as_object_mut().unwrap().remove("targetProfile");
        plan["target"] = target;
        fs::write(fixture.path("entry.impact.json"), plan.to_string()).unwrap();
        assert_eq!(
            failure(artifacts::assemble(
                fixture.recipe(),
                &fixture.path("bad-target-type")
            )),
            "profile_mismatch"
        );
        assert!(!fixture.path("bad-target-type").exists());
    }
}

#[test]
fn host_payload_budget_rejects_authenticated_total_before_payload_reads() {
    let fixture = Fixture::new();
    let manifest = fixture.assemble("bounded");
    let bytes = artifacts::manifest_bytes(&manifest).unwrap();
    let pin = artifacts::digest(&bytes);
    let root = fixture.path("bounded");
    let total = manifest.entries.iter().map(|e| e.size).sum::<u64>();
    assert!(artifacts::verify_with_limit(&root, Some(&pin), total).is_ok());
    for entry in &manifest.entries {
        fs::remove_file(root.join(&entry.path)).unwrap();
    }
    assert_eq!(
        failure(artifacts::verify_with_limit(&root, Some(&pin), total - 1)),
        "limit_exceeded"
    );
    assert_eq!(
        failure(artifacts::verify_with_limit(
            &root,
            Some(&"0".repeat(64)),
            total - 1
        )),
        "manifest_digest_mismatch"
    );
    assert_eq!(
        failure(artifacts::verify_with_limit(&root, Some(&pin), total)),
        "io_error"
    );
    assert_eq!(failure(artifacts::verify(&root, Some(&pin))), "io_error");
}
