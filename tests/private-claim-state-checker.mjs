// Native implementation samples complement the universal Lean state proofs.
import assert from 'node:assert/strict';
import {readFile} from 'node:fs/promises';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {pathToFileURL} from 'node:url';
import {resolve} from 'node:path';

const [checkerPath, planPath, callPath, ...extra] = process.argv.slice(2);
if (!checkerPath || !planPath || !callPath || extra.length)
  throw Error('Usage: node tests/private-claim-state-checker.mjs OFFICIAL_321_CHECKER PLAN_JSON CALL_ZKIR');
const require = createRequire(new URL('../scripts/zkir/package.json', import.meta.url));
const ledger = await import(pathToFileURL(require.resolve('@midnight-ntwrk/ledger-v9')).href);
const {Zkir, check} = await import(pathToFileURL(resolve(checkerPath)).href);
const atom = {tag: 'atom', value: {tag: 'field'}};
const field = n => ({value: ledger.bigIntToValue(n), alignment: [atom]});
const bool = b => ({value: [b ? Uint8Array.of(1) : new Uint8Array()], alignment: [{tag: 'atom', value: {tag: 'bytes', length: 1}}]});
const empty = {value: [], alignment: []};
const hash = values => ledger.valueToBigInt(ledger.transientHash(values.map(() => atom), values.flatMap(ledger.bigIntToValue)));
const secret = 42n, campaign = 9n, sibling0 = 17n, sibling1 = 23n;
const root = hash([2n, sibling1, hash([2n, hash([1n, secret, campaign]), sibling0])]);
const nullifier = hash([3n, secret, campaign]);
const planBytes = await readFile(planPath), callBytes = await readFile(callPath);
const plan = JSON.parse(planBytes), circuit = JSON.parse(callBytes);
assert.equal(plan.operations.length, 21);
assert.equal(circuit.instructions.length, 55);
assert.equal(circuit.do_communications_commitment, true);
const env = {root, campaign, suppliedNullifier: nullifier, nullifier, storedRoot: root, storedCampaign: campaign};
function expression(e) {
  switch (e.tag) {
    case 'reference': assert.ok(e.name in env); return env[e.name];
    case 'constant': return BigInt(e.value);
    case 'bool': return e.value ? 1n : 0n;
    case 'select': return expression(expression(e.condition) ? e.yes : e.no);
    default: throw Error(`unsupported fixture expression ${e.tag}`);
  }
}
const aligned = op => op.alignment === 'field' ? field(expression(op.expression)) : bool(Boolean(expression(op.expression)));
const operations = plan.operations.map(op => {
  switch (op.op) {
    case 'push': return {push: {storage: op.storage, value: {tag: 'cell', content: aligned(op)}}};
    case 'popeq': return {popeq: {cached: false, result: aligned(op)}};
    case 'dup': return {dup: {n: 0}};
    case 'index': return {idx: {cached: false, pushPath: op.pushPath, path: [{tag: 'value', value: field(BigInt(op.slot))}]}};
    case 'member': return 'member';
    case 'insert': return {ins: {cached: false, n: op.n}};
    default: throw Error(`unsupported fixture opcode ${op.op}`);
  }
});
const relation = Zkir.fromJson(JSON.stringify(circuit));
const provider = {lookupKey: async () => ({ir: relation.serialize(), proverKey: new Uint8Array(), verifierKey: new Uint8Array()})};
const preimage = ops => ledger.proofDataIntoSerializedPreimage(empty, empty, ops,
  [secret, sibling0, sibling1, 0n, 1n].map(field), 'noctium/state-preservation');
const activity = await check(preimage(operations), provider);
assert.equal(activity.length, 21);
assert.ok(activity.every(group => group === undefined || group === null), "every native group must be active");
const cost = ledger.CostModel.initialCostModel();
function context(storedRoot = root, storedCampaign = campaign, entries = []) {
  let map = new ledger.StateMap();
  for (const [key, value] of entries) map = map.insert(field(key), ledger.StateValue.newCell(field(value)));
  let state = ledger.StateValue.newArray();
  state = state.arrayPush(ledger.StateValue.newCell(field(storedRoot)));
  state = state.arrayPush(ledger.StateValue.newCell(field(storedCampaign)));
  state = state.arrayPush(ledger.StateValue.newMap(map));
  return new ledger.QueryContext(new ledger.ChargedState(state), ledger.dummyContractAddress());
}
const initial = context(root, campaign, [[333n, 1n]]);
const gather = operations.map(op => op.popeq ? {popeq: {...op.popeq, result: null}} : op);
const observed = initial.query(gather, cost);
const reads = observed.events.filter(e => e.tag === 'read').map(e => ledger.valueToBigInt(e.content.value));
assert.deepEqual(reads, [root, campaign, nullifier, root, campaign, 0n]);
const transcript = {gas: observed.gasCost, effects: observed.context.effects, program: operations};
const updated = initial.runTranscript(transcript, cost);
const slots = updated.state.state.asArray();
assert.equal(ledger.valueToBigInt(slots[0].asCell().value), root);
assert.equal(ledger.valueToBigInt(slots[1].asCell().value), campaign);
assert.equal(ledger.valueToBigInt(slots[2].asMap().get(field(nullifier)).asCell().value), 1n);
assert.equal(ledger.valueToBigInt(slots[2].asMap().get(field(333n)).asCell().value), 1n);
assert.equal(initial.state.state.asArray()[2].asMap().get(field(nullifier)), undefined);
assert.throws(() => updated.runTranscript(transcript, cost));
assert.throws(() => context(root + 1n).runTranscript(transcript, cost));
assert.throws(() => context(root, campaign + 1n).runTranscript(transcript, cost));
assert.throws(() => context(root, campaign, [[nullifier, 0n]]).runTranscript(transcript, cost));
// Exercise the same partition interface consumed by runtime/src/assembly.rs.
const parameters = ledger.LedgerParameters.initialParameters();
const randomness = ledger.communicationCommitmentRandomness();
const commitment = ledger.communicationCommitment(empty, empty, randomness);
const partitions = ledger.partitionTranscripts([new ledger.PreTranscript(initial, operations, commitment)], parameters);
assert.equal(partitions.length, 1);
const [guaranteed, fallible] = partitions[0];
assert.deepEqual([...(guaranteed?.program ?? []), ...(fallible?.program ?? [])], operations);
let partitioned = initial;
for (const segment of [guaranteed, fallible].filter(Boolean)) partitioned = partitioned.runTranscript(segment, cost);
assert.equal(ledger.valueToBigInt(partitioned.state.state.asArray()[2].asMap().get(field(nullifier)).asCell().value), 1n);
assert.equal(ledger.valueToBigInt(partitioned.state.state.asArray()[2].asMap().get(field(333n)).asCell().value), 1n);
const mutations = [
  ['slot', ops => {ops[7].idx.path[0].value = field(1n);}],
  ['path', ops => {ops[17].idx.pushPath = false;}],
  ['key', ops => {ops[18].push.value.content = field(nullifier + 1n);}],
  ['value', ops => {ops[19].push.value.content = field(0n);}],
  ['read', ops => {ops[8].popeq.result = field(root + 1n);}],
  ['opcode-group', ops => {[ops[6], ops[7]] = [ops[7], ops[6]];}],
  ['alignment', ops => {ops[16].popeq.result = field(0n);}],
  ['storage', ops => {ops[19].push.storage = false;}],
];
const results = [];
for (const [id, mutate] of mutations) {
  const changed = structuredClone(operations);
  mutate(changed);
  await assert.rejects(async () => check(preimage(changed), provider), undefined, id);
  results.push({id, nativeRelationRejected: true});
}
console.log(JSON.stringify({scope: 'local native ledger and official 3.2.1 checker samples',
  planSha256: createHash('sha256').update(planBytes).digest('hex'),
  callSha256: createHash('sha256').update(callBytes).digest('hex'),
  checkerSha256: createHash('sha256').update(await readFile(checkerPath)).digest('hex'),
  activity, allGroupsActive: true, partitionedOpcodeOrderPreserved: true,
  guaranteedOperations: guaranteed?.program.length ?? 0, fallibleOperations: fallible?.program.length ?? 0, readValues: reads.map(String), opcodeGroups: 21, exactSuccessor: true,
  replayRejected: true, wrongConfiguredRootRejected: true, wrongConfiguredCampaignRejected: true,
  presentFalseValueRejected: true, unrelatedEntryPreserved: true, initialStateUnchanged: true,
  emptyCommunicationCommitmentChecked: true, mutations: results,
  resourceScope: 'initial native CostModel and this finite fixture only',
  ledgerTransactionSubmitted: false, compiledContractVerified: false}, null, 2));
