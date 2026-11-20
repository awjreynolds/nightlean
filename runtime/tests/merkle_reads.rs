#![cfg(feature = "zkir-321")]

use base_crypto::{fab::AlignedValue, hash::HashOutput};
use noctium_runtime::{
    Db, artifacts, canonical_field,
    collection_ffi::noctium_ledger_collection_page,
    field_value,
    native_ffi::{
        INVALID_ARGUMENT, LIMIT, OK, noctium_native_result_copy, noctium_native_result_free,
        noctium_native_result_length,
    },
};
use onchain_runtime::state::{ChargedState, ContractState, StateValue};
use serde_json::{Value, json};
use serialize::tagged_serialize;
use std::{
    env, fs,
    path::PathBuf,
    process::Command,
    time::{SystemTime, UNIX_EPOCH},
};
use storage::arena::Sp;
use transient_crypto::{
    curve::Fr,
    merkle_tree::{MerkleTree, leaf_hash},
};

struct CppHost {
    binary: PathBuf,
    directory: PathBuf,
}

impl CppHost {
    fn from_env() -> Option<Self> {
        let binary = env::var_os("NOCTIUM_COLLECTION_CPP").map(PathBuf::from)?;
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .unwrap()
            .as_nanos();
        let directory = env::temp_dir().join(format!(
            "noctium-merkle-reads-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir_all(&directory).unwrap();
        Some(Self { binary, directory })
    }

    fn compare(&self, request: &[u8], plan: &[u8], snapshot: &[u8], status: i32, output: &[u8]) {
        let request_path = self.directory.join("request.json");
        let plan_path = self.directory.join("plan.json");
        let snapshot_path = self.directory.join("state.bin");
        fs::write(&request_path, request).unwrap();
        fs::write(&plan_path, plan).unwrap();
        fs::write(&snapshot_path, snapshot).unwrap();
        let cpp = Command::new(&self.binary)
            .args([request_path, plan_path, snapshot_path])
            .arg(status.to_string())
            .output()
            .unwrap();
        assert!(
            cpp.status.success(),
            "C++ collection ABI smoke failed: {}",
            String::from_utf8_lossy(&cpp.stderr)
        );
        assert_eq!(cpp.stdout, output);
    }
}

impl Drop for CppHost {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.directory);
    }
}

struct Snapshot {
    plan: Vec<u8>,
    state: Vec<u8>,
    cpp: Option<CppHost>,
}

impl Snapshot {
    fn new(plan: Vec<u8>, state: ChargedState<Db>) -> Self {
        let mut contract = ContractState::<Db>::default();
        contract.data = state;
        let mut state_bytes = Vec::new();
        tagged_serialize(&contract, &mut state_bytes).unwrap();
        Self {
            plan,
            state: state_bytes,
            cpp: CppHost::from_env(),
        }
    }

    fn page_request(&self, name: &str, keys: Value, offset: usize, limit: usize) -> Value {
        json!({"abiVersion":1,"planSha256":artifacts::digest(&self.plan),
            "stateSha256":artifacts::digest(&self.state),"name":name,
            "keys":keys,"offset":offset,"limit":limit})
    }

    fn path_request(&self, name: &str, keys: Value, leaf: Value, index: Option<&str>) -> Value {
        let mut path = json!({"leaf":leaf});
        if let Some(index) = index {
            path["index"] = json!(index);
        }
        json!({"abiVersion":1,"planSha256":artifacts::digest(&self.plan),
            "stateSha256":artifacts::digest(&self.state),"name":name,
            "keys":keys,"merklePath":path})
    }

    fn query(&self, request: &Value, expected_status: i32) -> Value {
        let request = serde_json::to_vec(request).unwrap();
        let mut token = 99;
        let output = unsafe {
            assert_eq!(
                noctium_ledger_collection_page(
                    request.as_ptr(),
                    request.len(),
                    self.plan.as_ptr(),
                    self.plan.len(),
                    self.state.as_ptr(),
                    self.state.len(),
                    &mut token,
                ),
                expected_status,
                "request {}",
                String::from_utf8_lossy(&request)
            );
            if expected_status == OK {
                let mut length = 0;
                assert_eq!(noctium_native_result_length(token, &mut length), OK);
                let mut output = vec![0; length];
                let mut written = 0;
                assert_eq!(
                    noctium_native_result_copy(token, output.as_mut_ptr(), length, &mut written),
                    OK
                );
                assert_eq!(written, length);
                assert_eq!(noctium_native_result_free(token), OK);
                Some(output)
            } else {
                assert_eq!(token, 0);
                None
            }
        };
        if let Some(cpp) = &self.cpp {
            cpp.compare(
                &request,
                &self.plan,
                &self.state,
                expected_status,
                output.as_deref().unwrap_or(&[]),
            );
        }
        output
            .map(|bytes| serde_json::from_slice(&bytes).unwrap())
            .unwrap_or(Value::Null)
    }
}

fn plan(state: Vec<Value>) -> Vec<u8> {
    let provenance: Value = serde_json::from_str(include_str!(
        "fixtures/issue65/PrivateClaim.claim-321.impact.json"
    ))
    .unwrap();
    serde_json::to_vec(&json!({
        "schemaVersion": 1,
        "target": provenance["target"],
        "targetProfile": provenance["targetProfile"],
        "state": state,
        "operations": [{"op":"merkleTreeInsertHash"}],
    }))
    .unwrap()
}

fn merkle_state(
    tree: MerkleTree<(), Db>,
    first_free: u64,
    historic_roots: Option<&[Fr]>,
) -> StateValue<Db> {
    let mut parts = vec![
        StateValue::BoundedMerkleTree(tree),
        StateValue::Cell(Sp::new(AlignedValue::from(first_free))),
    ];
    if let Some(roots) = historic_roots {
        parts.push(StateValue::Map(
            roots
                .iter()
                .copied()
                .map(|root| (field_value(root), StateValue::Null))
                .collect(),
        ));
    }
    StateValue::Array(parts.into())
}

fn tree(entries: &[(u64, [u8; 32])]) -> MerkleTree<(), Db> {
    let mut tree = MerkleTree::<(), Db>::blank(2);
    for (index, digest) in entries {
        tree = tree
            .try_update_hash(*index, HashOutput(*digest), ())
            .unwrap();
    }
    tree.rehash()
}

fn root_tree_state(tree: StateValue<Db>) -> ChargedState<Db> {
    ChargedState::new(StateValue::Array(vec![tree].into()))
}

fn nested_tree_state(ordinary: StateValue<Db>, archive: StateValue<Db>) -> ChargedState<Db> {
    let owner = AlignedValue::from([7u8; 32]);
    let bucket = field_value(Fr::from(1u64));
    let map = |tree| {
        StateValue::Map(
            [(
                owner.clone(),
                StateValue::Map([(bucket.clone(), tree)].into_iter().collect()),
            )]
            .into_iter()
            .collect(),
        )
    };
    ChargedState::new(StateValue::Array(vec![map(ordinary), map(archive)].into()))
}

fn nested_keys() -> Value {
    json!([
        {"type":"Bytes<32>","value":{"kind":"bytes","values":vec![7u8;32]}},
        {"type":"Native","value":"1"}
    ])
}

#[test]
fn merkle_reads_match_compact_vectors_and_nested_native_snapshots() {
    let vectors: Vec<Value> = serde_json::from_str(include_str!(
        "fixtures/merkle-curve-leaves/compact-0.36.1.json"
    ))
    .unwrap();
    assert_eq!(vectors.len(), 23);

    for vector in &vectors {
        let digest: [u8; 32] = hex::decode(vector["leafHash"].as_str().unwrap())
            .unwrap()
            .try_into()
            .unwrap();
        let root = canonical_field(vector["root"].as_str().unwrap()).unwrap();
        let leaf = &vector["leaf"];
        let history = [Fr::from(0u64), root];
        for historic in [false, true] {
            let snapshot = Snapshot::new(
                plan(vec![
                    json!({"name":"claims","kind":{"merkleTree":2,"historic":historic}}),
                ]),
                root_tree_state(merkle_state(
                    tree(&[(0, digest)]),
                    1,
                    historic.then_some(&history),
                )),
            );
            let found = snapshot.query(
                &snapshot.path_request("claims", json!([]), leaf.clone(), None),
                OK,
            );
            assert_eq!(found["candidateRoot"], vector["root"], "{vector}");
            assert_eq!(found["snapshotRoot"], vector["root"], "{vector}");
            assert_eq!(
                snapshot.query(
                    &snapshot.path_request("claims", json!([]), leaf.clone(), Some("0")),
                    OK
                ),
                found,
                "{vector}"
            );
        }
    }

    let zero_leaf = leaf_hash(&Fr::from(0u64)).0;
    let one_leaf = leaf_hash(&Fr::from(1u64)).0;
    let ordinary_root =
        "24384193648268865082143763383430680137169643988677567459801776720386725274219";
    let archive_root =
        "28177993292845671258227895926917860147375346170730846347234185481881467288296";
    let previous_archive_root =
        "35694116202192454536022596311527311726911393046632366691736512928127990181458";
    let nested = Snapshot::new(
        plan(vec![
            json!({"name":"ordinary","kind":{"tree":{"map":["Bytes<32>",{"map":["Native",{"merkleTree":2}]}]}}}),
            json!({"name":"archives","kind":{"tree":{"map":["Bytes<32>",{"map":["Native",{"merkleTree":2,"historic":true}]}]}}}),
        ]),
        nested_tree_state(
            merkle_state(tree(&[(0, [1; 32]), (2, zero_leaf)]), 3, None),
            merkle_state(
                tree(&[(0, one_leaf), (3, [3; 32])]),
                4,
                Some(&[
                    Fr::from(0u64),
                    canonical_field(previous_archive_root).unwrap(),
                    canonical_field(archive_root).unwrap(),
                ]),
            ),
        ),
    );
    let keys = nested_keys();
    let page = nested.query(&nested.page_request("ordinary", keys.clone(), 0, 1), OK);
    assert_eq!(page["root"], ordinary_root);
    assert_eq!(page["firstFree"], "3");
    let found = nested.query(
        &nested.path_request(
            "ordinary",
            keys.clone(),
            json!({"kind":"field","value":"0"}),
            None,
        ),
        OK,
    );
    assert_eq!(found["candidateRoot"], ordinary_root);
    assert_eq!(
        found["steps"],
        json!([
            {"sibling":"0","goesLeft":true},
            {"sibling":"4943352566282441417276972188451368878517305774466816738704609011908918842691","goesLeft":false}
        ])
    );
    assert_eq!(
        nested.query(
            &nested.path_request(
                "ordinary",
                keys.clone(),
                json!({"kind":"field","value":"0"}),
                Some("2")
            ),
            OK,
        ),
        found
    );
    let changed = nested.query(
        &nested.path_request(
            "ordinary",
            keys.clone(),
            json!({"kind":"field","value":"999"}),
            Some("2"),
        ),
        OK,
    );
    assert_eq!(
        changed["candidateRoot"],
        "10296121656604956664794135251423149705089531830531534764270364168513922163116"
    );
    assert_eq!(changed["steps"], found["steps"]);
    let missing = nested.query(
        &nested.path_request(
            "ordinary",
            keys.clone(),
            json!({"kind":"field","value":"999"}),
            None,
        ),
        OK,
    );
    assert_eq!(missing["candidateRoot"], Value::Null);
    assert_eq!(missing["steps"], Value::Null);

    assert_eq!(
        nested.query(
            &nested.path_request(
                "ordinary",
                keys.clone(),
                json!({"kind":"field","value":"777"}),
                Some("3")
            ),
            OK,
        )["candidateRoot"],
        "35385881896919654727748289961498738103298950063057740844106476655315710292372"
    );

    let archive = nested.query(
        &nested.path_request(
            "archives",
            keys.clone(),
            json!({"kind":"field","value":"1"}),
            None,
        ),
        OK,
    );
    assert_eq!(archive["candidateRoot"], archive_root);
    assert_eq!(archive["snapshotRoot"], archive_root);
    let archive_changed = nested.query(
        &nested.path_request(
            "archives",
            keys.clone(),
            json!({"kind":"field","value":"999"}),
            Some("0"),
        ),
        OK,
    );
    assert_eq!(
        archive_changed["candidateRoot"],
        "16280196853999604315943632376308786576597348417781226905764274764903286704971"
    );
    assert_eq!(archive_changed["steps"], archive["steps"]);

    let prehashed = json!({"kind":"prehashed","value":vec![3u8; 32]});
    assert_eq!(
        nested.query(
            &nested.path_request("archives", keys.clone(), prehashed.clone(), Some("3")),
            OK,
        )["candidateRoot"],
        archive_root
    );
    let first = nested.query(&nested.page_request("archives", keys.clone(), 0, 2), OK);
    let second = nested.query(&nested.page_request("archives", keys.clone(), 2, 2), OK);
    assert_eq!(first["root"], archive_root);
    assert_eq!(first["firstFree"], "4");
    assert_eq!(first["nextOffset"], 2);
    assert_eq!(second["nextOffset"], Value::Null);
    let mut roots = first["entries"]
        .as_array()
        .unwrap()
        .iter()
        .chain(second["entries"].as_array().unwrap())
        .map(|root| root.as_str().unwrap())
        .collect::<Vec<_>>();
    roots.sort_unstable();
    assert_eq!(roots, ["0", archive_root, previous_archive_root]);

    let mut bad_digest = nested.page_request("ordinary", keys.clone(), 0, 1);
    bad_digest["stateSha256"] = json!("00".repeat(32));
    nested.query(&bad_digest, INVALID_ARGUMENT);
    nested.query(
        &nested.path_request(
            "ordinary",
            keys.clone(),
            json!({"kind":"field","value":"0"}),
            Some("4"),
        ),
        INVALID_ARGUMENT,
    );
    nested.query(
        &nested.path_request("ordinary", keys, json!({"kind":"field","value":"52435875175126190479447740508185965837690552500527637822603658699938581184513"}), None),
        INVALID_ARGUMENT,
    );
    let oversized_fab = json!({"kind":"fab","value":{"value":[[]],"alignment":[
        {"tag":"atom","value":{"tag":"bytes","length":1048577}}
    ]}});
    for bad in [oversized_fab, json!({"kind":"jubjubPoint","x":"0","y":"0"})] {
        nested.query(
            &nested.path_request("ordinary", nested_keys(), bad, None),
            INVALID_ARGUMENT,
        );
    }
    let too_many_roots = nested.page_request("archives", nested_keys(), 0, 65);
    nested.query(&too_many_roots, LIMIT);
}
