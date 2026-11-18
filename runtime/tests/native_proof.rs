//! Native caller qualification. No child process, Node runtime, network, or filesystem in core.
use futures::{
    executor::block_on,
    future::{pending, ready},
};
use ledger::structure::{ContractAction, ProofVersioned};
use noctium_runtime::{
    artifacts,
    assembly::NativeIntent,
    proof::{
        Abort, Error, LocalProver, PreparedProof, ProofRequest, ProofService, ServiceError,
        TrustedParameters,
    },
};
use rand::rngs::OsRng;
use serialize::{Deserializable, tagged_deserialize, tagged_serialize};
use sha2::{Digest, Sha256};
use std::{cell::Cell, fs};
use transient_crypto::curve::Fr;

struct Response {
    bytes: Vec<u8>,
    calls: Cell<usize>,
    payload_digest: Cell<Option<[u8; 32]>>,
}
impl Response {
    fn new(bytes: Vec<u8>) -> Self {
        Self {
            bytes,
            calls: Cell::new(0),
            payload_digest: Cell::new(None),
        }
    }
}
impl ProofService for Response {
    async fn prove(&self, request: ProofRequest<'_>) -> Result<Vec<u8>, ServiceError> {
        self.calls.set(self.calls.get() + 1);
        let payload = request.private_wire_payload().map_err(|_| ServiceError)?;
        assert!(!payload.is_empty());
        self.payload_digest
            .set(Some(Sha256::digest(&payload).into()));
        Ok(self.bytes.clone())
    }
}
struct Never {
    polled: Cell<bool>,
    dropped: Cell<bool>,
}
impl ProofService for Never {
    async fn prove(&self, _: ProofRequest<'_>) -> Result<Vec<u8>, ServiceError> {
        self.polled.set(true);
        struct Guard<'a>(&'a Cell<bool>);
        impl Drop for Guard<'_> {
            fn drop(&mut self) {
                self.0.set(true);
            }
        }
        let _guard = Guard(&self.dropped);
        pending().await
    }
}
fn encoded<T: serialize::Serializable + serialize::Tagged>(value: &T) -> Vec<u8> {
    let mut result = Vec::new();
    tagged_serialize(value, &mut result).unwrap();
    result
}
fn native(prepared: &PreparedProof) -> NativeIntent {
    tagged_deserialize(prepared.private_intent_bytes().unwrap().as_slice()).unwrap()
}

#[test]
fn parameter_identity_and_fixed_errors_reject_without_echoing_private_values() {
    for bytes in [b"SENTINEL_PRIVATE_VALUE".as_slice(), &[]] {
        let error = TrustedParameters::from_bytes(bytes, 9, &"0".repeat(64))
            .err()
            .unwrap();
        assert!(!format!("{error:#} {error:?}").contains("SENTINEL"));
    }
    let error = ServiceError;
    assert_eq!(format!("{error}"), "noctium_proof_service_failure");
}

#[test]
fn authenticated_malformed_parameters_reject_before_unchecked_native_read() {
    let digest = |bytes: &[u8]| hex::encode(Sha256::digest(bytes));
    // Infinity is a valid point encoding, but this synthetic file is not a trusted SRS.
    // Ceremony provenance and the relations between points belong to the host trust root.
    let mut encoding = 1u32.to_le_bytes().to_vec();
    for size in [96, 96, 96, 96, 192, 192] {
        let mut infinity = vec![0; size];
        infinity[0] = 0x40;
        encoding.extend(infinity);
    }
    assert!(TrustedParameters::from_bytes(&encoding, 1, &digest(&encoding)).is_ok());
    let mut cases = vec![
        vec![255, 0, 0, 0],
        vec![1, 0, 0],
        encoding[..encoding.len() - 1].to_vec(),
    ];
    let mut trailing = encoding.clone();
    trailing.push(0);
    cases.push(trailing);
    let mut wrong_header = encoding.clone();
    wrong_header[..4].copy_from_slice(&255u32.to_le_bytes());
    cases.push(wrong_header);
    for offset in [4, 4 + 3 * 96, 4 + 4 * 96, 4 + 4 * 96 + 192] {
        let mut invalid_point = encoding.clone();
        invalid_point[offset..offset + 96].fill(255);
        cases.push(invalid_point);
    }
    for bytes in cases {
        assert_eq!(
            TrustedParameters::from_bytes(&bytes, 1, &digest(&bytes)).err(),
            Some(Error::InvalidParameters)
        );
    }
}

#[test]
#[ignore = "requires authenticated source claim bundle with real native keys"]
fn authenticated_malformed_keys_reject_before_private_input() {
    use artifacts::{Manifest, Role};
    use midnight_zk_stdlib::Relation;
    let source = std::path::PathBuf::from(std::env::var("NOCTIUM_TEST_BUNDLE").unwrap());
    let manifest: Manifest =
        serde_json::from_slice(&fs::read(source.join("manifest.json")).unwrap()).unwrap();
    let root = std::env::temp_dir().join(format!(
        "noctium-malformed-key-{}",
        rand::Rng::r#gen::<u64>(&mut OsRng)
    ));
    fs::create_dir(&root).unwrap();
    let root = fs::canonicalize(root).unwrap();
    struct Cleanup(std::path::PathBuf);
    impl Drop for Cleanup {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let _cleanup = Cleanup(root.clone());
    for entry in &manifest.entries {
        let path = root.join(&entry.path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::copy(source.join(&entry.path), path).unwrap();
    }
    for role in [Role::ProverKey, Role::VerifierKey] {
        let index = manifest
            .entries
            .iter()
            .position(|entry| entry.role == role)
            .unwrap();
        let original = fs::read(source.join(&manifest.entries[index].path)).unwrap();
        let prefix_end = original
            .iter()
            .enumerate()
            .filter(|(_, byte)| **byte == b':')
            .nth(1)
            .unwrap()
            .0
            + 1;
        let mut reader = &original[prefix_end..];
        let size = u32::deserialize(&mut reader, 0).unwrap() as usize;
        assert_eq!(reader.len(), size);
        let payload_offset = original.len() - size;
        let degree_offset = if role == Role::ProverKey {
            payload_offset
        } else {
            midnight_zk_stdlib::ZkStdLibArch::read(&mut reader).unwrap();
            original.len() - reader.len()
        };
        let mut cases = vec![original[..original.len() - 1].to_vec()];
        for degree in [0, 255] {
            let mut bytes = original.clone();
            bytes[degree_offset] = degree;
            cases.push(bytes);
        }
        let mut trailing = original.clone();
        trailing.push(0);
        cases.push(trailing);
        let mut bad_encoding = original.clone();
        if role == Role::VerifierKey {
            bad_encoding[payload_offset + 4] = 255; // Invalid architecture boolean.
        } else {
            bad_encoding[payload_offset + 1] ^= 1; // Embedded relation must match retained IR exactly.
        }
        cases.push(bad_encoding);
        let body_offset = if role == Role::ProverKey {
            let circuit_entry = manifest
                .entries
                .iter()
                .find(|entry| entry.role == Role::Circuit)
                .unwrap();
            let circuit = noctium_runtime::zkir::IrSource::load(
                fs::read(source.join(&circuit_entry.path))
                    .unwrap()
                    .as_slice(),
            )
            .unwrap();
            let mut relation = Vec::new();
            circuit.write_relation(&mut relation).unwrap();
            let offset = payload_offset + 1 + relation.len();
            let mut cs = midnight_proofs::plonk::ConstraintSystem::default();
            midnight_zk_stdlib::ZkStdLib::configure(
                &mut cs,
                (circuit.used_chips(), original[degree_offset] - 1),
            );
            let columns =
                cs.num_fixed_columns() + cs.num_selectors() + cs.permutation().get_columns().len();
            let polynomials = offset + 6 + columns * 96;
            for field in [polynomials, polynomials + 4] {
                let mut bytes = original.clone();
                bytes[field..field + 4].fill(255);
                cases.push(bytes);
            }
            let mut bad_scalar = original.clone();
            bad_scalar[polynomials + 8..polynomials + 40].fill(255);
            cases.push(bad_scalar);
            offset
        } else {
            degree_offset + 5
        };
        let mut bad_inner_degree = original.clone();
        bad_inner_degree[body_offset + 1] = 0;
        cases.push(bad_inner_degree);
        let mut huge_columns = original.clone();
        huge_columns[body_offset + 2..body_offset + 6].fill(255);
        cases.push(huge_columns);
        let mut invalid_point = original.clone();
        invalid_point[body_offset + 6..body_offset + 54].fill(255);
        cases.push(invalid_point);
        for (case_index, bytes) in cases.into_iter().enumerate() {
            let mut changed = manifest.clone();
            changed.entries[index].size = bytes.len() as u64;
            changed.entries[index].sha256 = artifacts::digest(&bytes);
            fs::write(root.join(&changed.entries[index].path), bytes).unwrap();
            let encoded = artifacts::manifest_bytes(&changed).unwrap();
            fs::write(root.join("manifest.json"), &encoded).unwrap();
            let bundle = artifacts::verify(&root, Some(&artifacts::digest(&encoded))).unwrap();
            assert_eq!(
                PreparedProof::from_config(
                    &bundle,
                    b"SENTINEL_PRIVATE_VALUE",
                    2_000_000_000,
                    &mut OsRng
                )
                .err(),
                Some(Error::InvalidArtifacts),
                "{role:?} mutation {case_index}"
            );
        }
        fs::write(root.join(&manifest.entries[index].path), original).unwrap();
    }
}

#[test]
#[ignore = "requires authenticated source claim bundle, private config, and trusted native SRS"]
fn actual_source_claim_proves_verifies_and_attaches_without_subprocesses() {
    let root = std::env::var("NOCTIUM_TEST_BUNDLE").unwrap();
    let digest = std::env::var("NOCTIUM_TEST_MANIFEST_SHA256").unwrap();
    let config = fs::read(std::env::var("NOCTIUM_TEST_PRIVATE_CONFIG").unwrap()).unwrap();
    let parameter_bytes =
        fs::read(std::env::var("NOCTIUM_TEST_PROOF_PARAMETERS").unwrap()).unwrap();
    let parameter_digest = std::env::var("NOCTIUM_TEST_PROOF_PARAMETERS_SHA256").unwrap();
    let integrity_only = artifacts::verify(root.as_ref(), None).unwrap();
    assert_eq!(
        PreparedProof::from_config(
            &integrity_only,
            b"SENTINEL_PRIVATE_VALUE",
            2_000_000_000,
            &mut OsRng
        )
        .err(),
        Some(Error::UnauthenticatedBundle)
    );
    assert!(artifacts::verify(root.as_ref(), Some(&"0".repeat(64))).is_err());
    let bundle = artifacts::verify(root.as_ref(), Some(&digest)).unwrap();
    assert_eq!(
        bundle.authenticated_manifest_sha256(),
        Some(digest.as_str())
    );
    let prepared = PreparedProof::from_config(&bundle, &config, 2_000_000_000, &mut OsRng).unwrap();
    let malformed = PreparedProof::from_config(
        &bundle,
        br#"{"inputs":"SENTINEL_PRIVATE_VALUE"}"#,
        2_000_000_000,
        &mut OsRng,
    )
    .err()
    .unwrap();
    assert_eq!(malformed, Error::InvalidPrivateInput);
    assert!(!format!("{malformed:#}").contains("SENTINEL"));
    let params =
        TrustedParameters::from_bytes(&parameter_bytes, prepared.k(), &parameter_digest).unwrap();
    assert_eq!(params.k(), prepared.k());
    assert_eq!(params.sha256(), parameter_digest);
    assert_eq!(
        TrustedParameters::from_bytes(&parameter_bytes, prepared.k() + 1, &parameter_digest).err(),
        Some(Error::InvalidParameters)
    );
    assert!(prepared.deployment_intent().is_some());
    assert_eq!(prepared.profile(), noctium_runtime::profile::NAME);

    // An already-triggered stop prevents the service from seeing private material.
    let response = Response::new(vec![]);
    for abort in [Abort::Cancelled, Abort::Deadline] {
        let expected = if abort == Abort::Cancelled {
            Error::Cancelled
        } else {
            Error::Deadline
        };
        assert_eq!(
            block_on(prepared.prove(&response, &params, 1_048_576, ready(abort))).err(),
            Some(expected)
        );
    }
    assert_eq!(response.calls.get(), 0);
    // A pending request is dropped after the host cancellation future fires.
    let never = Never {
        polled: Cell::new(false),
        dropped: Cell::new(false),
    };
    let stop = futures::future::poll_fn(|cx| {
        if never.polled.get() {
            std::task::Poll::Ready(Abort::Cancelled)
        } else {
            cx.waker().wake_by_ref();
            std::task::Poll::Pending
        }
    });
    assert_eq!(
        block_on(prepared.prove(&never, &params, 1_048_576, stop)).err(),
        Some(Error::Cancelled)
    );
    assert!(never.dropped.get());

    let local = LocalProver::new(OsRng);
    let proved = block_on(prepared.prove(&local, &params, 1_048_576, pending())).unwrap();
    let roundtrip: noctium_runtime::proof::ProvedNativeIntent =
        tagged_deserialize(proved.serialized()).unwrap();
    assert_eq!(encoded(&roundtrip), proved.serialized());
    let ContractAction::Call(call) = proved.native().actions.iter_deref().next().unwrap() else {
        panic!("expected call")
    };
    let ProofVersioned::V3(proof) = &call.proof else {
        panic!("expected native ledger V3 proof")
    };
    let wire = encoded(&ProofVersioned::V2(proof.clone()));
    let public_bytes = proved.public_serialized().unwrap();
    let public: noctium_runtime::proof::PublicProvedNativeIntent =
        tagged_deserialize(public_bytes.as_slice()).unwrap();
    assert_eq!(encoded(&public), public_bytes);
    assert_eq!(
        public.binding_commitment,
        proved.native().binding_commitment.into()
    );
    let ContractAction::Call(public_call) = public.actions.iter_deref().next().unwrap() else {
        panic!("expected public call")
    };
    assert_eq!(
        public_call
            .public_inputs(public.binding_commitment)
            .unwrap(),
        call.public_inputs(proved.native().binding_commitment.into())
            .unwrap()
    );
    let pulled = prepared
        .private_request_payload(&params, 1_048_576)
        .unwrap();
    let replay = Response::new(wire.clone());
    assert!(block_on(prepared.prove(&replay, &params, 1_048_576, pending())).is_ok());
    assert_eq!(
        replay.payload_digest.get(),
        Some(Sha256::digest(&pulled).into())
    );
    let attached = block_on(prepared.attach_response(&params, &wire, 1_048_576)).unwrap();
    assert_eq!(attached.serialized(), proved.serialized());
    println!(
        "native_bridge_sizes payload={} response={} attached={}",
        pulled.len(),
        wire.len(),
        attached.serialized().len()
    );
    // The entropy-owning local adapter is one-use. A retry needs a fresh adapter.
    assert_eq!(
        block_on(prepared.prove(&local, &params, 1_048_576, pending())).err(),
        Some(Error::Service)
    );

    let mut corrupted = proof.clone();
    corrupted.0[0] ^= 1;
    let mut unknown_version = wire.clone();
    let discriminant_offset = wire.len() - proof.0.len() - 5;
    unknown_version[discriminant_offset] = 255;
    let mut huge_declared_vector = wire.clone();
    huge_declared_vector[discriminant_offset + 1..discriminant_offset + 5]
        .copy_from_slice(&u32::MAX.to_le_bytes());
    let cases = [
        (vec![], Error::Limit),
        (vec![0; 1_048_577], Error::Limit),
        (wire[..wire.len() - 1].to_vec(), Error::InvalidResponse),
        (
            {
                let mut bytes = wire.clone();
                bytes.push(0);
                bytes
            },
            Error::InvalidResponse,
        ),
        (
            encoded(&ProofVersioned::V3(proof.clone())),
            Error::InvalidResponse,
        ),
        (unknown_version, Error::InvalidResponse),
        (huge_declared_vector, Error::InvalidResponse),
        (encoded(&ProofVersioned::V2(corrupted)), Error::InvalidProof),
    ];
    for (bytes, expected) in cases {
        assert_eq!(
            block_on(prepared.prove(&Response::new(bytes), &params, 1_048_576, pending())).err(),
            Some(expected)
        );
    }
    assert_eq!(
        block_on(prepared.prove(&Response::new(wire.clone()), &params, 0, pending())).err(),
        Some(Error::Limit)
    );

    // Exact contract identity feeds native binding. A proof for the first address fails here.
    let mut wrong_contract = native(&prepared);
    let mut actions: Vec<_> = wrong_contract.actions.iter_deref().cloned().collect();
    let ContractAction::Call(call) = &mut actions[0] else {
        unreachable!()
    };
    let mut changed = (**call).clone();
    changed.address.0.0[0] ^= 1;
    *call = storage::arena::Sp::new(changed);
    wrong_contract.actions = actions.into();
    let wrong_contract = PreparedProof::from_intent(&bundle, wrong_contract).unwrap();
    assert_eq!(
        block_on(wrong_contract.prove(&Response::new(wire.clone()), &params, 1_048_576, pending()))
            .err(),
        Some(Error::InvalidProof)
    );

    // The parent intent binding commitment also changes the exact statement.
    let mut wrong_binding = native(&prepared);
    wrong_binding.binding_commitment = rand::Rng::r#gen(&mut OsRng);
    let wrong_binding = PreparedProof::from_intent(&bundle, wrong_binding).unwrap();
    assert_eq!(
        block_on(wrong_binding.prove(&Response::new(wire.clone()), &params, 1_048_576, pending()))
            .err(),
        Some(Error::InvalidProof)
    );

    let mut wrong_communication = native(&prepared);
    let mut actions: Vec<_> = wrong_communication.actions.iter_deref().cloned().collect();
    let ContractAction::Call(call) = &mut actions[0] else {
        unreachable!()
    };
    let mut changed = (**call).clone();
    changed.communication_commitment = call.communication_commitment + Fr::from(1u64);
    *call = storage::arena::Sp::new(changed);
    wrong_communication.actions = actions.into();
    // No response service sees material after a preimage/call commitment mismatch.
    assert_eq!(
        PreparedProof::from_intent(&bundle, wrong_communication).err(),
        Some(Error::BindingMismatch)
    );
}
