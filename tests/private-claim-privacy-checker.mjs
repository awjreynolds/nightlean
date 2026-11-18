// A genuine Poseidon symmetric-path pair. This tests public observations,
// not proof-byte zero knowledge or host/provider confidentiality.
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {pathToFileURL} from 'node:url';
import {resolve, dirname, join} from 'node:path';

const [checkerPath, planPath, callPath, ...extra] = process.argv.slice(2);
if (!checkerPath || !planPath || !callPath || extra.length)
  throw Error('Usage: node tests/private-claim-privacy-checker.mjs OFFICIAL_321_CHECKER PLAN_JSON CALL_ZKIR');
const require = createRequire(new URL('../scripts/zkir/package.json', import.meta.url));
const ledger = await import(pathToFileURL(require.resolve('@midnight-ntwrk/ledger-v9')).href);
const {Zkir, check} = await import(pathToFileURL(resolve(checkerPath)).href);
const atom = {tag: 'atom', value: {tag: 'field'}};
const field = n => ({value: ledger.bigIntToValue(n), alignment: [atom]});
const bit = b => ({value: [b ? Uint8Array.of(1) : new Uint8Array()], alignment: [{tag: 'atom', value: {tag: 'bytes', length: 1}}]});
const empty = {value: [], alignment: []};
const hash = values => ledger.valueToBigInt(ledger.transientHash(values.map(() => atom), values.flatMap(ledger.bigIntToValue)));
const secret = 42n, campaign = 9n, sibling1 = 23n;
const leaf = hash([1n, secret, campaign]);
const sibling0 = leaf;
const node = hash([2n, leaf, leaf]);
const root = hash([2n, sibling1, node]);
const nullifier = hash([3n, secret, campaign]);
const planBytes = await readFile(planPath), callBytes = await readFile(callPath);
const plan = JSON.parse(planBytes), circuit = JSON.parse(callBytes);
assert.equal(plan.operations.length, 21);
assert.equal(circuit.instructions.length, 55);
const env = {root, campaign, nullifier, suppliedNullifier: nullifier, storedRoot: root, storedCampaign: campaign};
function expression(e) {
  switch (e.tag) {
    case 'reference': assert.ok(e.name in env); return env[e.name];
    case 'constant': return BigInt(e.value);
    case 'bool': return e.value ? 1n : 0n;
    case 'select': return expression(expression(e.condition) ? e.yes : e.no);
    default: throw Error(`unsupported expression ${e.tag}`);
  }
}
const aligned = op => op.alignment === 'field' ? field(expression(op.expression)) : bit(Boolean(expression(op.expression)));
const operations = plan.operations.map(op => {
  switch (op.op) {
    case 'push': return {push: {storage: op.storage, value: {tag: 'cell', content: aligned(op)}}};
    case 'popeq': return {popeq: {cached: false, result: aligned(op)}};
    case 'dup': return {dup: {n: 0}};
    case 'index': return {idx: {cached: false, pushPath: op.pushPath, path: [{tag: 'value', value: field(BigInt(op.slot))}]}};
    case 'member': return 'member';
    case 'insert': return {ins: {cached: false, n: op.n}};
    default: throw Error(`unsupported operation ${op.op}`);
  }
});
const relation = Zkir.fromJson(JSON.stringify(circuit));
const provider = {lookupKey: async () => ({ir: relation.serialize(), proverKey: new Uint8Array(), verifierKey: new Uint8Array()})};
let state = ledger.StateValue.newArray();
state = state.arrayPush(ledger.StateValue.newCell(field(root)));
state = state.arrayPush(ledger.StateValue.newCell(field(campaign)));
state = state.arrayPush(ledger.StateValue.newMap(new ledger.StateMap()));
const address = ledger.dummyContractAddress();
const initial = new ledger.QueryContext(new ledger.ChargedState(state), address);
const parameters = ledger.LedgerParameters.initialParameters();
let randomness;
do {randomness = ledger.communicationCommitmentRandomness();} while (randomness === "00");
const commitment = ledger.communicationCommitment(empty, empty, randomness);
const partitions = ledger.partitionTranscripts([new ledger.PreTranscript(initial, operations, commitment)], parameters);
assert.equal(partitions.length, 1);
const [guaranteed, fallible] = partitions[0];
const parentIntent = ledger.Intent.new(new Date(2000000000 * 1000));
const unwrap = call => {
  const versioned = Buffer.from(call.proof.serialize());
  const wrapper = Buffer.from("midnight:proof-preimage-versioned:");
  assert.deepEqual(versioned.subarray(0, wrapper.length), wrapper);
  assert.equal(versioned[wrapper.length], 1, "expected native ProofPreimageVersioned::V2");
  return Buffer.concat([Buffer.from("midnight:proof-preimage:"), versioned.subarray(wrapper.length + 1)]);
};
const operation = new ledger.ContractOperation();
const calls = [];
for (const direction0 of [0n, 1n]) {
  const privateValues = [secret, sibling0, sibling1, direction0, 1n];
  const prototype = new ledger.ContractCallPrototype(address, 'claim', operation, guaranteed, fallible,
    privateValues.map(field), empty, empty, randomness, 'noctium/privacy-pair');
  const intent = parentIntent.addCall(prototype);
  const action = intent.actions[0];
  assert.ok(action instanceof ledger.ContractCall);
  const call = action;
  const proofPreimage = unwrap(call);
  // Deprecated intoCall uses the randomness as commitment. Never substitute it.
  await assert.rejects(async () => check(unwrap(prototype.intoCall(new ledger.PreBinding("00"))), provider),
    /Communications commitment mismatch/);
  const activity = await check(proofPreimage, provider);
  assert.equal(activity.length, 21);
  assert.ok(activity.every(group => group === undefined || group === null));
  let updated = initial;
  for (const transcript of [call.guaranteedTranscript, call.fallibleTranscript].filter(Boolean))
    updated = updated.runTranscript(transcript, ledger.CostModel.initialCostModel());
  assert.equal(ledger.valueToBigInt(updated.state.state.asArray()[2].asMap().get(field(nullifier)).asCell().value), 1n);
  calls.push({call, proofPreimage, activity, updated, privateValues});
}
// SCALE scalar vectors in the pinned public ProofPreimage serialization.
function publicPreimage(bytes) {
  bytes = Buffer.from(bytes);
  const prefix = Buffer.from('midnight:proof-preimage:');
  assert.deepEqual(bytes.subarray(0, prefix.length), prefix);
  let position = prefix.length;
  function scalar() {
    const first = bytes[position], mode = first & 3;
    let size, value = 0n;
    if (mode < 3) {
      size = [1, 2, 4][mode];
      for (let i = size - 1; i >= 0; i--) value = (value << 8n) | BigInt(bytes[position + i]);
      position += size;
      return value >> 2n;
    }
    size = (first >> 2) + 4;
    position++;
    for (let i = size - 1; i >= 0; i--) value = (value << 8n) | BigInt(bytes[position + i]);
    position += size;
    return value;
  }
  const vector = () => Array.from({length: Number(scalar())}, scalar);
  const inputs = vector(), privateValues = vector(), publicGroups = vector(), publicReads = vector(), binding = scalar();
  assert.equal(bytes[position++], 1);
  const communicationCommitment = scalar(), communicationRandomness = scalar();
  return {inputs, privateValues, publicGroups, publicReads, binding, communicationCommitment, communicationRandomness};
}
const [left, right] = calls.map(x => publicPreimage(x.proofPreimage));
assert.notEqual(left.communicationRandomness, 0n);
assert.equal(left.binding, 0n, "constructor binding is a proof-phase placeholder");
assert.notDeepEqual(left.privateValues, right.privateValues);
assert.deepEqual(left.privateValues.slice(0, 3), right.privateValues.slice(0, 3));
assert.notEqual(left.privateValues[3], right.privateValues[3]);
const publicOnly = ({privateValues, ...publicFields}) => publicFields;
assert.deepEqual(publicOnly(left), publicOnly(right));
assert.deepEqual(left.publicReads, [root, campaign, nullifier, root, campaign, 0n]);
assert.deepEqual(calls[0].call.guaranteedTranscript.program, calls[1].call.guaranteedTranscript.program);
assert.equal(calls[0].call.communicationCommitment, calls[1].call.communicationCommitment);
assert.deepEqual(calls[0].activity, calls[1].activity);
assert.equal(calls[0].updated.state.state.toString(true), calls[1].updated.state.state.toString(true));
assert.equal(calls[0].updated.state.state.asArray().length, 3);
const changedCoin = ledger.communicationCommitmentRandomness();
assert.notEqual(ledger.communicationCommitment(empty, empty, changedCoin), commitment);
const json = value => JSON.stringify(value, (_, item) => typeof item === 'bigint' ? String(item) : item);
console.log(JSON.stringify({scope: 'successful native public-call observation pair under shared host coins and parent binding',
  checkerModuleSha256: createHash('sha256').update(await readFile(checkerPath)).digest('hex'),
  checkerWasmSha256: createHash('sha256').update(await readFile(join(dirname(resolve(checkerPath)), 'midnight_zkir_wasm_bg.wasm'))).digest('hex'),
  ledgerAdapterVersion: JSON.parse(await readFile(join(dirname(require.resolve('@midnight-ntwrk/ledger-v9')), 'package.json'))).version,
  ledgerAdapterModuleSha256: createHash('sha256').update(await readFile(require.resolve('@midnight-ntwrk/ledger-v9'))).digest('hex'),
  planSha256: createHash('sha256').update(planBytes).digest('hex'),
  callSha256: createHash('sha256').update(callBytes).digest('hex'),
  publicFixture: {secret: String(secret), campaign: String(campaign), sibling0: String(sibling0), sibling1: String(sibling1),
    root: String(root), nullifier: String(nullifier), directions: [[0, 1], [1, 1]]},
  genuinePoseidon: true, symmetricPath: true, bothOfficialCheckerAccepted: true,
  actualConstructorPreimagesChecked: true, assemblyPath: "Intent.addCall", deprecatedIntoCallRejected: true,
  nonzeroCommunicationRandomness: true, differingPrivateDirection: true,
  orderedOpcodePayloadsEqual: true, readValuesEqual: true, queryPathsEqual: true,
  nativeSuccessorEqual: true, allActivityEqual: true, emptyCommunicationCommitmentEqual: true,
  constructorBindingPlaceholdersEqual: true, constructorBindingPlaceholder: "0", sharedParentIntent: true, coupledHostCoins: true,
  finalProofPhaseBindingOverrideVerified: false, finalBindingImplementationAgreementRequired: true,
  publicStatementSha256: createHash('sha256').update(json(publicOnly(left))).digest('hex'),
  unpairedCoinsChangeObservation: true, proofBytesZeroKnowledgeProved: false,
  byteParserCertificate: false, deploymentIdentity: false, compiledContractVerified: false}, null, 2));
