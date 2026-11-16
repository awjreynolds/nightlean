#![cfg(all(feature = "localnet", feature = "zkir-321"))]
//! Public-only adversarial joins against real audited source/key/deployment fixtures.
use futures::executor::block_on;
use nightlean_runtime::{
    Db,
    artifacts::{self, Role},
    deployment_audit::{self as audit, DeploymentRecord, Specification},
    localnet::Node,
};
use onchain_runtime::state::{ContractOperation, ContractState, EntryPointBuf};
use serde_json::json;
use std::{
    fs,
    path::{Path, PathBuf},
    time::Duration,
};
fn copy_tree(from: &Path, to: &Path) {
    fs::create_dir(to).unwrap();
    for item in fs::read_dir(from).unwrap() {
        let item = item.unwrap();
        let path = item.path();
        assert!(!path.is_symlink());
        if path.is_dir() {
            copy_tree(&path, &to.join(item.file_name()));
        } else {
            fs::copy(path, to.join(item.file_name())).unwrap();
        }
    }
}
fn changed_bundle(
    root: &Path,
    name: &str,
    role: Option<Role>,
    bytes: &[u8],
    source_revision: bool,
) -> (PathBuf, String) {
    let target = root.join(name);
    copy_tree(&root.join("public/native-bundle"), &target);
    let mut manifest: artifacts::Manifest =
        serde_json::from_slice(&fs::read(target.join("manifest.json")).unwrap()).unwrap();
    if let Some(role) = role {
        let entry = manifest
            .entries
            .iter_mut()
            .find(|x| x.role == role)
            .unwrap();
        entry.size = bytes.len() as u64;
        entry.sha256 = artifacts::digest(bytes);
        fs::write(target.join(&entry.path), bytes).unwrap();
    }
    if source_revision {
        manifest.compiler.source_revision = "0".repeat(40);
    }
    let bytes = artifacts::manifest_bytes(&manifest).unwrap();
    fs::write(target.join("manifest.json"), &bytes).unwrap();
    (target, artifacts::digest(&bytes))
}
#[test]
#[ignore = "requires the public issue56/57 qualification bundle and authorized loopback node"]
fn actual_public_identity_join_rejects_refreshed_manifests_and_revision_mutants() {
    block_on(async {
        let root = PathBuf::from(std::env::var("NOCTIUM_DEPLOYMENT_TEST_ROOT").unwrap());
        let spec_bytes = fs::read(root.join("specification.json")).unwrap();
        let spec: Specification = serde_json::from_slice(&spec_bytes).unwrap();
        let authority = fs::read(std::env::var("NOCTIUM_DEPLOYMENT_AUTHORITY").unwrap()).unwrap();
        let tool = fs::read(std::env::var("NOCTIUM_DEPLOYMENT_NATIVE_TOOLCHAIN").unwrap()).unwrap();
        let srs = fs::read(std::env::var("NOCTIUM_DEPLOYMENT_SRS").unwrap()).unwrap();
        let other = fs::read(std::env::var("NOCTIUM_DEPLOYMENT_OTHER_VERIFIER").unwrap()).unwrap();
        let package: serde_json::Value =
            serde_json::from_slice(&fs::read(root.join("public/manifest.json")).unwrap()).unwrap();
        let bundle = artifacts::verify(
            &root.join("public/native-bundle"),
            package["nativeManifestSha256"].as_str(),
        )
        .unwrap();
        let material = audit::qualify(&spec, &authority, &bundle, &srs, &tool)
            .await
            .unwrap();
        let initial = material.initial_bytes().unwrap();
        let native: ContractState<Db> = audit::decode(&initial).unwrap();
        assert!(
            native
                .operations
                .get(&EntryPointBuf(b"claim".to_vec()))
                .unwrap()
                .v3_vk()
                .is_some()
        );
        assert!(
            native
                .operations
                .get(&EntryPointBuf(b"claim".to_vec()))
                .unwrap()
                .v2_vk()
                .is_none()
        );
        let node = Node::connect(
            "http://127.0.0.1:19944",
            spec.policy.clone(),
            Duration::from_secs(30),
            64 * 1024 * 1024,
            100_000,
        )
        .unwrap();
        material.check_parameter_reference(&spec, &node).unwrap();
        let snapshot = node.sync().unwrap();
        let quote = material
            .check_live(&spec, &snapshot, node.runtime_fingerprint())
            .unwrap();
        assert_eq!(
            audit::hash(&hex::decode(&quote.ledger_parameters_hex).unwrap()),
            quote.ledger_parameters_sha256
        );
        let mut results = Vec::new();
        for (name, role, bytes, revision) in [
            ("wrong-key", Some(Role::VerifierKey), other.clone(), false),
            ("wrong-source-revision", None, vec![], true),
            (
                "wrong-source-bytes",
                Some(Role::Source),
                b"-- independent wrong source\n".to_vec(),
                false,
            ),
        ] {
            let (path, pin) = changed_bundle(&root, name, role, &bytes, revision);
            let mutant = artifacts::verify(&path, Some(&pin)).unwrap();
            assert!(
                audit::qualify(&spec, &authority, &mutant, &srs, &tool)
                    .await
                    .is_err(),
                "{name}"
            );
            fs::remove_dir_all(path).unwrap();
            results.push(name);
        }
        for (name, mutant) in [
            ("wrong-srs", {
                let mut x = spec.clone();
                x.srs_sha256 = "0".repeat(64);
                x
            }),
            ("wrong-ledger-parameters", {
                let mut x = spec.clone();
                x.ledger_parameters_sha256 = "0".repeat(64);
                x
            }),
            ("wrong-authority", {
                let mut x = spec.clone();
                x.authority_sha256 = "0".repeat(64);
                x
            }),
            ("wrong-entrypoint", {
                let mut x = spec.clone();
                x.entrypoint = "other".into();
                x
            }),
            ("wrong-target", {
                let mut x = spec.clone();
                x.policy.profile = "midnight-ledger-9".into();
                x
            }),
        ] {
            assert!(
                audit::qualify(&mutant, &authority, &bundle, &srs, &tool)
                    .await
                    .is_err(),
                "{name}"
            );
            results.push(name);
        }
        let mut wrong_network = spec.clone();
        wrong_network.policy.genesis = "0".repeat(64);
        assert!(
            material
                .check_live(&wrong_network, &snapshot, node.runtime_fingerprint())
                .is_err()
        );
        results.push("wrong-network");
        let mut bad = native.clone();
        let mut init = spec.initialization.clone();
        init.insert("acceptedRoot".into(), json!("0"));
        bad.data = nightlean_runtime::create_state(&material.plan, &init).unwrap();
        assert!(
            material
                .check_initial(&audit::encode(&bad).unwrap())
                .is_err()
        );
        results.push("wrong-initialization");
        let replacement: transient_crypto::proofs::VerifierKey = audit::decode(&other).unwrap();
        let mut upgraded = native.clone();
        upgraded.operations = upgraded.operations.insert(
            EntryPointBuf(b"claim".to_vec()),
            ContractOperation::new(Some(replacement), None),
        );
        assert!(
            material
                .check_revision(&audit::encode(&upgraded).unwrap())
                .is_err()
        );
        results.push("new-key-at-same-address");
        let mut restored = native.clone();
        restored.maintenance_authority.counter += 1;
        assert!(
            material
                .check_revision(&audit::encode(&restored).unwrap())
                .is_err()
        );
        results.push("restored-key-after-maintenance");
        let mut pinned: ledger::structure::LedgerParameters =
            audit::decode(bundle.file(Role::LedgerParameters).unwrap()).unwrap();
        pinned.fee_prices.overall_price =
            pinned.fee_prices.overall_price + base_crypto::cost_model::FixedPoint::ONE;
        let mutated = audit::encode(&pinned).unwrap();
        assert_ne!(mutated, bundle.file(Role::LedgerParameters).unwrap());
        assert_ne!(audit::hash(&mutated), spec.ledger_parameters_sha256);
        assert_ne!(
            node.finalized_ledger_parameters_at(
                &spec.ledger_parameters_block_hash,
                spec.ledger_parameters_height
            )
            .unwrap(),
            mutated
        );
        results.push("mutated-historical-fee-price");
        let mut record: DeploymentRecord =
            serde_json::from_slice(&fs::read(root.join("execution/deployment.json")).unwrap())
                .unwrap();
        assert!(
            audit::observe_record(
                &spec,
                &spec_bytes,
                &material,
                &record,
                &"0".repeat(64),
                &node
            )
            .is_err()
        );
        results.push("wrong-address");
        let mut quoted: ledger::structure::LedgerParameters = audit::decode(
            &hex::decode(&record.deployment.funding_quote.ledger_parameters_hex).unwrap(),
        )
        .unwrap();
        quoted.fee_prices.overall_price =
            quoted.fee_prices.overall_price + base_crypto::cost_model::FixedPoint::ONE;
        record.deployment.funding_quote.ledger_parameters_hex =
            hex::encode(audit::encode(&quoted).unwrap());
        record.deployment.funding_quote.ledger_parameters_sha256 =
            audit::hash(&audit::encode(&quoted).unwrap());
        assert!(
            audit::observe_record(
                &spec,
                &spec_bytes,
                &material,
                &record,
                &record.address,
                &node
            )
            .is_err()
        );
        results.push("forged-live-quote-with-refreshed-hash");
        fs::write(root.join("negative-results.json"),serde_json::to_vec_pretty(&json!({"scope":"public native join/revision regressions, no private inputs or live maintenance update","rejected":results,"laterNativePriceQuoteMatched":true,"laterQuoteSha256":quote.ledger_parameters_sha256,"historicalParameterSha256":spec.ledger_parameters_sha256})).unwrap()).unwrap();
    });
}
