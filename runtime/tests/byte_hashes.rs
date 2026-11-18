#![cfg(feature = "zkir-321")]

use noctium_runtime::zkir::IrSource;
use noctium_runtime::{Expr, Plan, check, create_state, field_value, prepare};
use onchain_runtime::state::StateValue;
use serde_json::json;
use sha2::{Digest, Sha512};
use sha3::Keccak256;
use std::borrow::Cow;
use std::collections::BTreeMap;
use transient_crypto::{
    curve::Fr,
    proofs::{KeyLocation, ProofPreimage, Zkir},
};

#[test]
fn native_hashes_accept_empty_fab_preimages() {
    for (opcode, digest) in [
        ("sha512", Sha512::digest([]).to_vec()),
        ("keccak256", Keccak256::digest([]).to_vec()),
    ] {
        for alignment in [
            json!([]),
            json!([{"tag":"atom","value":{"tag":"bytes","length":0}}]),
        ] {
            let names: Vec<_> = (0..digest.len().div_ceil(31))
                .map(|index| format!("%chunk{index}"))
                .collect();
            let mut instructions = vec![
                json!({"op":opcode,"alignment":alignment,"inputs":[],"output":"%digest"}),
                json!({"op":"encode","input":"%digest","outputs":names}),
            ];
            for (name, bytes) in names.iter().zip(digest.chunks(31)) {
                instructions.push(
                    json!({"op":"constrain_eq","a":name,"b":format!("0x{}",hex::encode(bytes))}),
                );
            }
            instructions.push(json!({"op":"output","vals":[]}));
            let source = json!({"version":{"major":3,"minor":2},"inputs":[],"outputs":[],"do_communications_commitment":false,"instructions":instructions});
            let source = serde_json::to_vec(&source).unwrap();
            let circuit = IrSource::load(source.as_slice()).unwrap();
            if alignment.as_array().unwrap().is_empty() {
                assert!(circuit.k() > 0);
            }
            let preimage = ProofPreimage {
                inputs: vec![],
                private_transcript: vec![],
                public_transcript_inputs: vec![],
                public_transcript_outputs: vec![],
                binding_input: Fr::from(0u64),
                communications_commitment: None,
                key_location: KeyLocation(Cow::Borrowed("noctium/empty-byte-hash")),
            };
            preimage.check(&circuit).unwrap();
        }
    }
}

#[test]
fn source_hashes_bind_full_preimages_and_typed_digest_results() {
    let plan: Plan = serde_json::from_str(include_str!(
        "fixtures/byte-hashes/321/ByteHashes.inspect.impact.json"
    ))
    .unwrap();
    let circuit = IrSource::load(
        include_bytes!("fixtures/byte-hashes/321/ByteHashes.inspect.zkir").as_slice(),
    )
    .unwrap();
    let names = [
        "sha31First",
        "sha31Last",
        "sha32First",
        "sha32Last",
        "sha33First",
        "sha33Last",
        "keccak31First",
        "keccak31Last",
        "keccak32First",
        "keccak32Last",
        "keccak33First",
        "keccak33Last",
        "shaWindowFirst",
        "shaWindowLast",
    ];
    let initial = create_state(
        &plan,
        &names
            .iter()
            .map(|name| ((*name).into(), json!("0")))
            .collect(),
    )
    .unwrap();
    let payload: Vec<u8> = (0..64).collect();
    let inputs = BTreeMap::from([
        ("payload".into(), json!({"kind":"bytes","values":payload})),
        ("enabled".into(), json!(true)),
    ]);
    let mut execution = prepare(
        &plan,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    check(&execution, &circuit).unwrap();
    let value = |digest: Vec<u8>| json!({"kind":"bytes","values":digest});
    assert_eq!(
        execution.returns_json(),
        BTreeMap::from([
            ("shaEmpty".into(), value(Sha512::digest([]).to_vec())),
            ("keccakEmpty".into(), value(Keccak256::digest([]).to_vec())),
            ("shaAbc".into(), value(Sha512::digest(b"abc").to_vec())),
            (
                "keccakAbc".into(),
                value(Keccak256::digest(b"abc").to_vec())
            ),
            (
                "shaPayload".into(),
                value(Sha512::digest(&payload).to_vec())
            ),
            (
                "keccakPayload".into(),
                value(Keccak256::digest(&payload).to_vec())
            ),
        ])
    );
    let mut expected = Vec::new();
    for length in [31, 32, 33] {
        let digest = Sha512::digest(&payload[..length]);
        expected.extend([digest[0], digest[63]]);
    }
    for length in [31, 32, 33] {
        let digest = Keccak256::digest(&payload[..length]);
        expected.extend([digest[0], digest[31]]);
    }
    let sha = Sha512::digest(&payload);
    expected.extend([sha[31], sha[63]]);
    let StateValue::Array(state) = execution.after.state.get_ref() else {
        panic!("expected state array");
    };
    for (index, byte) in expected.into_iter().enumerate() {
        let StateValue::Cell(cell) = state.get(index).unwrap() else {
            panic!("expected byte cell");
        };
        assert_eq!(**cell, field_value(Fr::from(byte as u64)));
    }
    execution.preimage.private_transcript[63] = Fr::from(62u64);
    assert!(check(&execution, &circuit).is_err());
    execution.preimage.private_transcript[63] = Fr::from(63u64);
    execution.preimage.private_transcript[64] = Fr::from(0u64);
    assert!(check(&execution, &circuit).is_err());
    let mut forged = plan.clone();
    forged.returns[3].expression = Expr::BytesLiteral {
        length: 32,
        values: sha3::Sha3_256::digest(b"abc").to_vec(),
    };
    let forged = prepare(
        &forged,
        &inputs,
        &initial,
        &ledger::structure::INITIAL_PARAMETERS,
        coin_structure::contract::ContractAddress::default(),
    )
    .unwrap();
    assert!(check(&forged, &circuit).is_err());
    assert_eq!(
        hex::encode(Keccak256::digest([])),
        "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470"
    );
}
