use super::{Operation, Pair, bytes32, checked_call, development_policy};
use base_crypto::hash::HashOutput;
use coin_structure::contract::ContractAddress;
use futures::executor::block_on;
use ledger::structure::LedgerState;
use noctium_runtime::{
    Db,
    assembly::CompositionOffer,
    field_decimal,
    localnet::Node,
    prepare,
    proof::{CompositionDraft, Error, IndependentComposition, ProvedIntent},
};
use onchain_runtime::state::ContractState;
use rand::{Rng, rngs::OsRng};
use serde_json::{Value as Json, json};
use std::{
    collections::BTreeMap,
    env,
    io::{self, BufRead, BufReader, Read, Write},
    path::PathBuf,
    process::{Child, ChildStdin, ChildStdout, Command, Stdio},
    time::Duration,
};
use transient_crypto::{curve::Fr, hash::transient_hash, proofs::Zkir};

const OWNER_SLOT: &str = "NOCTIUM_COMPOSITION_OWNER_SLOT";
const REPLY: &str = "NOCTIUM_OWNER ";

fn read_line(reader: &mut impl BufRead) -> Option<String> {
    let mut line = String::new();
    let size = reader.take(34 * 1024 * 1024).read_line(&mut line).unwrap();
    if size == 0 {
        return None;
    }
    assert!(line.ends_with('\n'), "incomplete owner frame");
    Some(line)
}

fn receive(reader: &mut impl BufRead) -> Json {
    while let Some(line) = read_line(reader) {
        if let Some((_, message)) = line.split_once(REPLY) {
            return serde_json::from_str(message).unwrap();
        }
    }
    panic!("owner stopped before replying")
}

fn send(writer: &mut impl Write, value: Json) {
    writeln!(writer, "{value}").unwrap();
    writer.flush().unwrap();
}

struct Worker {
    process: Child,
    input: ChildStdin,
    output: BufReader<ChildStdout>,
}

impl Worker {
    fn spawn(index: usize) -> Self {
        let mut process = Command::new(env::current_exe().unwrap())
            .args(["--exact", "owner::owner_worker", "--ignored", "--nocapture"])
            .env(OWNER_SLOT, index.to_string())
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let input = process.stdin.take().unwrap();
        let output = BufReader::new(process.stdout.take().unwrap());
        Self {
            process,
            input,
            output,
        }
    }

    fn send(&mut self, value: Json) {
        send(&mut self.input, value);
    }

    fn receive(&mut self) -> Json {
        receive(&mut self.output)
    }
}

impl Drop for Worker {
    fn drop(&mut self) {
        let _ = self.process.kill();
        let _ = self.process.wait();
    }
}

pub(super) struct Owners {
    parent: Worker,
    callee: Worker,
    pub credentials: [Json; 2],
}

impl Owners {
    pub fn spawn() -> Self {
        let mut parent = Worker::spawn(0);
        let mut callee = Worker::spawn(1);
        assert_ne!(parent.process.id(), callee.process.id());
        let credentials = [parent.receive(), callee.receive()];
        assert!(credentials.iter().all(Json::is_string));
        assert_ne!(credentials[0], credentials[1]);
        Self {
            parent,
            callee,
            credentials,
        }
    }

    pub fn compose(
        &mut self,
        pair: &Pair,
        snapshot: &LedgerState<Db>,
        ttl: u64,
    ) -> (ProvedIntent, Json) {
        let callee_address = pair.callee.deploy.address();
        self.callee.send(json!({
            "address": hex::encode(callee_address.0.0),
            "ttl": ttl,
        }));
        let callee_bytes = payload(&self.callee.receive());
        let callee = CompositionOffer::from_public_bytes(&callee_bytes).unwrap();
        let parent_address = pair.caller.deploy.address();
        self.parent.send(json!({
            "address": hex::encode(parent_address.0.0),
            "target": bytes32(callee_address.0),
            "entryHash": bytes32(pair.callee.entry.ep_hash()),
            "commitment": field_decimal(callee.commitment()),
        }));
        let parent_bytes = payload(&self.parent.receive());
        let parent = CompositionOffer::from_public_bytes(&parent_bytes).unwrap();
        let offers = [parent, callee];
        assert!(IndependentComposition::freeze(&offers[..1], snapshot, ttl, &mut OsRng).is_err());
        let coordinator =
            IndependentComposition::freeze(&offers, snapshot, ttl, &mut OsRng).unwrap();
        let draft = coordinator.draft().public_bytes().unwrap();
        let mut corrupted = draft.clone();
        *corrupted.last_mut().unwrap() ^= 1;
        assert_eq!(
            CompositionDraft::from_public_bytes(&corrupted, snapshot).err(),
            Some(Error::BindingMismatch)
        );
        let request = json!(hex::encode(&draft));
        self.parent.send(request.clone());
        self.callee.send(request);
        let proofs = [
            payload(&self.parent.receive()),
            payload(&self.callee.receive()),
        ];
        for worker in [&mut self.parent, &mut self.callee] {
            assert!(
                worker.process.wait().unwrap().success(),
                "proof owner failed"
            );
        }

        let selected = pair.materials();
        let other = IndependentComposition::freeze(&offers, snapshot, ttl, &mut OsRng).unwrap();
        assert_eq!(
            other.attach(&proofs, snapshot, &selected).err(),
            Some(Error::InvalidProof)
        );
        let proved = coordinator.attach(&proofs, snapshot, &selected).unwrap();
        (
            proved,
            json!({
                "proverProcesses": 2,
                "proverHosts": ["Rust", if env::var_os("NOCTIUM_COMPOSITION_CPP_OWNER").is_some() {
                    "C++"
                } else {
                    "Rust"
                }],
                "offerBytes": [parent_bytes.len(), callee_bytes.len()],
                "draftBytes": draft.len(),
                "proofBytes": [proofs[0].len(), proofs[1].len()],
                "alteredDraftRejected": true,
                "differentCommitmentRejected": true,
                "wrongOwnerSlotRejected": true,
            }),
        )
    }
}

fn payload(value: &Json) -> Vec<u8> {
    hex::decode(value.as_str().expect("expected encoded public bytes")).unwrap()
}

fn write_frame(writer: &mut impl Write, bytes: &[u8]) {
    let length = u32::try_from(bytes.len()).unwrap().to_be_bytes();
    writer.write_all(&length).unwrap();
    writer.write_all(bytes).unwrap();
}

fn read_frame(reader: &mut impl Read, max_bytes: usize) -> Vec<u8> {
    let mut length = [0u8; 4];
    reader.read_exact(&mut length).unwrap();
    let size = u32::from_be_bytes(length) as usize;
    assert!((1..=max_bytes).contains(&size));
    let mut bytes = vec![0; size];
    reader.read_exact(&mut bytes).unwrap();
    bytes
}

#[test]
#[ignore = "internal child process for the funded independent-prover test"]
fn owner_worker() {
    let Ok(slot) = env::var(OWNER_SLOT) else {
        return;
    };
    let (index, role, entry) = match slot.as_str() {
        "0" => (0, "caller", "claim"),
        "1" => (1, "callee", "advance"),
        _ => panic!("unknown owner"),
    };
    let secret: Fr = OsRng.r#gen();
    let credential = json!(field_decimal(transient_hash(&[secret])));
    let input = io::stdin();
    let mut input = input.lock();
    let reply = |message: Json| {
        println!("{REPLY}{message}");
        io::stdout().flush().unwrap();
    };
    let mut initial = BTreeMap::from([("acceptedCredential".into(), credential.clone())]);
    if index == 1 {
        initial.extend([
            ("balance".into(), json!("10")),
            ("count".into(), json!("0")),
        ]);
    }
    reply(credential.clone());
    let command: Json = serde_json::from_str(&read_line(&mut input).unwrap()).unwrap();
    let address_bytes: [u8; 32] = payload(&command["address"]).try_into().unwrap();
    let address = ContractAddress(HashOutput(address_bytes));
    let node = Node::connect(
        &env::var("NOCTIUM_COMPOSITION_NODE").unwrap(),
        development_policy(),
        Duration::from_secs(30),
        64 * 1024 * 1024,
        100_000,
    )
    .unwrap();
    let observed = node
        .finalized_contract_state(command["address"].as_str().unwrap())
        .unwrap();
    let contract: ContractState<Db> = serialize::tagged_deserialize(&observed.bytes[..]).unwrap();
    let params = node
        .finalized_ledger_parameters_at(&observed.block_hash, observed.height)
        .unwrap();
    let mut snapshot = LedgerState::<Db>::new(observed.chain.network_id.clone());
    snapshot.parameters =
        storage::arena::Sp::new(serialize::tagged_deserialize(&params[..]).unwrap());
    snapshot.contract = snapshot.contract.insert(address, contract.clone());

    let operation = Operation::load(role, entry, initial);
    let mut inputs = BTreeMap::from([
        ("credential".into(), credential),
        ("secret".into(), json!(field_decimal(secret))),
    ]);
    if index == 0 {
        for name in ["target", "entryHash", "commitment"] {
            inputs.insert(name.into(), command[name].clone());
        }
    } else {
        inputs.insert("amount".into(), json!("3"));
    }
    if let Some(cpp) = env::var_os("NOCTIUM_COMPOSITION_CPP_OWNER").filter(|_| index == 1) {
        let bundle_root = PathBuf::from(env::var_os("NOCTIUM_COMPOSITION_BUNDLES").unwrap());
        let srs_root = PathBuf::from(env::var_os("NOCTIUM_COMPOSITION_SRS").unwrap());
        let k = operation.circuit.k();
        let srs = std::fs::read(srs_root.join(format!("bls_midnight_2p{k}"))).unwrap();
        let descriptor = json!({
            "abiVersion": 1,
            "profile": observed.chain.profile,
            "bundleDirectory": bundle_root.join("callee-bundle"),
            "trustedManifestSha256": env::var("NOCTIUM_COMPOSITION_CALLEE_SHA256").unwrap(),
            "proofParametersSha256": env::var("NOCTIUM_COMPOSITION_CALLEE_SRS_SHA256").unwrap(),
            "networkId": observed.chain.network_id,
            "contractAddress": command["address"],
            "k": k,
            "ttl": command["ttl"],
        });
        let mut child = Command::new(cpp)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .unwrap();
        let mut request = child.stdin.take().unwrap();
        let mut response = child.stdout.take().unwrap();
        let private_inputs = zeroize::Zeroizing::new(serde_json::to_vec(&inputs).unwrap());
        for bytes in [
            serde_json::to_vec(&descriptor).unwrap().as_slice(),
            private_inputs.as_slice(),
            &observed.bytes,
            &params,
            &srs,
        ] {
            write_frame(&mut request, bytes);
        }
        request.flush().unwrap();
        drop(private_inputs);
        reply(json!(hex::encode(read_frame(
            &mut response,
            4 * 1024 * 1024
        ))));
        let draft = payload(&serde_json::from_str(&read_line(&mut input).unwrap()).unwrap());
        write_frame(&mut request, &draft);
        drop(request);
        let proof = read_frame(&mut response, 1024 * 1024);
        assert!(child.wait().unwrap().success(), "C++ proof owner failed");
        reply(json!(hex::encode(proof)));
        return;
    }
    let execution = prepare(
        &operation.plan,
        &inputs,
        &contract.data,
        &snapshot.parameters,
        address,
    )
    .unwrap();
    let call = checked_call(
        &execution,
        &operation.circuit,
        contract.data,
        address,
        operation.entry.clone(),
        OsRng.r#gen(),
    );
    let offer = call.composition_offer(&snapshot.parameters).unwrap();
    reply(json!(hex::encode(offer.public_bytes().unwrap())));

    let draft_bytes = payload(&serde_json::from_str(&read_line(&mut input).unwrap()).unwrap());
    let draft = CompositionDraft::from_public_bytes(&draft_bytes, &snapshot).unwrap();
    let material = operation.proof_selection();
    assert_eq!(
        block_on(draft.prove_call(1 - index, &call, &snapshot, &material, OsRng)).err(),
        Some(Error::BindingMismatch)
    );
    let proof = block_on(draft.prove_call(index, &call, &snapshot, &material, OsRng)).unwrap();
    reply(json!(hex::encode(proof)));
}
