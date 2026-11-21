#![cfg(feature = "zkir-321")]

use coin_structure::contract::ContractAddress;
use ledger::structure::INITIAL_PARAMETERS;
use noctium_runtime::{
    check, create_state, field_decimal, merkle::merkle_tree_at, prepare, zkir::IrSource, Db, Plan,
};
use onchain_runtime::state::ChargedState;
use serde_json::{json, Value as Json};
use std::{collections::BTreeMap, env, fs::File, path::PathBuf};

type Fixture = (Plan, IrSource);

const CURVES: [(&str, &str, &str); 9] = [
    ("k1Base", "Secp256k1Base", "k1BaseTree"),
    ("k1Scalar", "Secp256k1Scalar", "k1ScalarTree"),
    ("k1Point", "Secp256k1Point", "k1PointTree"),
    ("r1Base", "Secp256r1Base", "r1BaseTree"),
    ("r1Scalar", "Secp256r1Scalar", "r1ScalarTree"),
    ("r1Point", "Secp256r1Point", "r1PointTree"),
    ("c255Base", "Curve25519Base", "c255BaseTree"),
    ("c255Scalar", "Curve25519Scalar", "c255ScalarTree"),
    ("c255Point", "Curve25519Point", "c255PointTree"),
];

fn fixture() -> Fixture {
    let directory = PathBuf::from(
        env::var_os("NOCTIUM_FOREIGN_MERKLE_DIR")
            .expect("set fresh outputs in NOCTIUM_FOREIGN_MERKLE_DIR"),
    );
    let stem = "ForeignMerkleLeaves.append";
    let plan = serde_json::from_slice(
        &std::fs::read(directory.join(format!("{stem}.impact.json"))).unwrap(),
    )
    .unwrap();
    let circuit =
        IrSource::load(File::open(directory.join(format!("{stem}.zkir"))).unwrap()).unwrap();
    (plan, circuit)
}

fn representative_bytes(ty: &str) -> Vec<u8> {
    match ty {
        "Secp256k1Point" => {
            hex::decode("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")
                .unwrap()
        }
        "Secp256r1Point" => {
            hex::decode("036b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296")
                .unwrap()
        }
        "Curve25519Point" => [vec![0x58], vec![0x66; 31]].concat(),
        _ => [vec![1], vec![0; 31]].concat(),
    }
}

fn vector<'a>(vectors: &'a [Json], ty: &str) -> &'a Json {
    let bytes = representative_bytes(ty);
    vectors
        .iter()
        .find(|vector| {
            vector["leaf"]["kind"] == "foreign"
                && vector["leaf"]["type"] == ty
                && vector["leaf"]["bytes"] == json!(bytes)
        })
        .unwrap_or_else(|| panic!("missing pinned Compact representative vector for {ty}"))
}

fn inputs(vectors: &[Json]) -> BTreeMap<String, Json> {
    CURVES
        .iter()
        .map(|(input, ty, _)| ((*input).to_owned(), vector(vectors, ty)["leaf"].clone()))
        .collect()
}

fn run(
    (plan, circuit): &Fixture,
    arguments: &BTreeMap<String, Json>,
    state: &ChargedState<Db>,
) -> noctium_runtime::Execution {
    let execution = prepare(
        plan,
        arguments,
        state,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    )
    .unwrap_or_else(|error| panic!("{}: {error}", plan.entrypoint));
    check(&execution, circuit).unwrap_or_else(|error| panic!("{}: {error}", plan.entrypoint));
    execution
}

#[test]
#[ignore = "requires fresh ForeignMerkleLeaves outputs in NOCTIUM_FOREIGN_MERKLE_DIR"]
fn foreign_curve_merkle_appends_match_compact_nonzero_leaf_vectors() {
    let fixture = fixture();
    let vectors: Vec<Json> = serde_json::from_str(include_str!(
        "fixtures/merkle-curve-leaves/compact-0.36.1.json"
    ))
    .unwrap();
    let arguments = inputs(&vectors);
    let initial = create_state(
        &fixture.0,
        &CURVES
            .iter()
            .map(|(_, _, tree)| ((*tree).to_owned(), json!([])))
            .collect(),
    )
    .unwrap();

    let appended = run(&fixture, &arguments, &initial).after.state;
    for (_, ty, tree_name) in CURVES {
        let vector = vector(&vectors, ty);
        let digest: [u8; 32] = hex::decode(vector["leafHash"].as_str().unwrap())
            .unwrap()
            .try_into()
            .unwrap();
        let snapshot = merkle_tree_at(&fixture.0.state, &appended, tree_name, &[]).unwrap();
        let view = snapshot.view().unwrap();
        assert_eq!(view.first_free, 1, "{tree_name} cursor");
        assert_eq!(field_decimal(view.root), vector["root"].as_str().unwrap());
        let path = snapshot.prehashed_path(0, digest).unwrap();
        assert_eq!(path.leaf_hash(), &digest, "{tree_name} leaf digest");
        assert_eq!(field_decimal(path.root()), vector["root"].as_str().unwrap());
    }

    let mut full = appended;
    for _ in 1..4 {
        full = run(&fixture, &arguments, &full).after.state;
    }
    let error = match prepare(
        &fixture.0,
        &arguments,
        &full,
        &INITIAL_PARAMETERS,
        ContractAddress::default(),
    ) {
        Ok(_) => panic!("the fifth append must fail"),
        Err(error) => error,
    };
    assert!(error.to_string().contains("MerkleTree is full"));
}
