import assert from 'node:assert/strict';
import { readFile } from 'node:fs/promises';
import * as ledger from '@midnight-ntwrk/ledger-v9';
import * as zkir from '@midnightntwrk/zkir-v3';

const [operationsPath, circuitPath, ...extra] = process.argv.slice(2);
if (!operationsPath || !circuitPath || extra.length) {
  console.error('Usage: node check-impact.mjs <Impact fixture JSON> <native entrypoint ZKIR>');
  process.exit(1);
}

const atom = { tag: 'atom', value: { tag: 'field' } };
const field = n => ({ value: ledger.bigIntToValue(n), alignment: [atom] });
const empty = { value: [], alignment: [] };
const hash = values => ledger.valueToBigInt(ledger.transientHash(
  values.map(() => atom), values.flatMap(ledger.bigIntToValue)));

// This public test fixture uses secret=42, campaign=7, siblings=[17,23],
// directions=[false,true]. Domain tags are Nightlean choices, not ledger constants.
const secret = 42n;
const campaign = 7n;
const leaf = hash([1n, secret, campaign]);
const node = hash([2n, leaf, 17n]);
const root = hash([2n, 23n, node]);
const nullifier = hash([3n, secret, campaign]);

function hydrate(value) {
  if (Array.isArray(value)) return value.map(hydrate);
  if (!value || typeof value !== 'object') return value;
  const result = Object.fromEntries(Object.entries(value).map(([k, v]) => [k, hydrate(v)]));
  if (Array.isArray(result.value) && Array.isArray(result.alignment)) {
    result.value = result.value.map(bytes => Uint8Array.from(bytes));
    if (result.alignment[0]?.value?.tag === 'field') {
      const number = ledger.valueToBigInt(result.value);
      if (number === 99n) result.value = field(root).value;
      if (number === 123n) result.value = field(nullifier).value;
    }
  }
  return result;
}

const operations = hydrate(JSON.parse(await readFile(operationsPath, 'utf8')));
const source = await readFile(circuitPath, 'utf8');
assert.equal(JSON.parse(source).do_communications_commitment, true,
  'native ContractCall verification always requires a communication commitment');
const relation = zkir.Zkir.fromJson(source);
const provider = {
  lookupKey: async () => ({ ir: relation.serialize(),
    proverKey: new Uint8Array(), verifierKey: new Uint8Array() }),
};
const reads = operations.flatMap(op => op.popeq ? [op.popeq.result] : []);
assert.equal(reads.length, 6, 'expected the fixed claim fixture with six public reads');
assert.deepEqual(reads.map(v => ledger.valueToBigInt(v.value)),
  [root, campaign, nullifier, root, campaign, 0n]);

const preimage = (ops = operations, witness = secret) =>
  ledger.proofDataIntoSerializedPreimage(empty, empty, ops,
    [witness, 17n, 23n, 0n, 1n].map(field), 'nightlean/direct-impact');
const accepted = await zkir.check(preimage(), provider);
assert.equal(accepted.length, operations.length,
  'the ledger needs one activity group per native VM operation');

async function expectRelationRejection(name, ops, witness = secret) {
  await assert.rejects(async () => zkir.check(preimage(ops, witness), provider),
    /Failed direct assertion/, `${name} must fail the relation`);
}

// Mutate a call parameter's push and matching read, preserving a coherent VM
// public parameter operation while breaking the proved relation/state guard.
function changedParameter(index, value) {
  return operations.map((op, i) => {
    if (i === index * 2) return { push: { ...op.push,
      value: { tag: 'cell', content: field(value) } } };
    if (i === index * 2 + 1) return { popeq: { ...op.popeq, result: field(value) } };
    return op;
  });
}
function changedRead(index, value) {
  let position = 0;
  return operations.map(op => {
    if (!op.popeq) return op;
    return position++ === index ? { popeq: { ...op.popeq, result: field(value) } } : op;
  });
}

await expectRelationRejection('wrong secret', operations, 43n);
await expectRelationRejection('wrong public root', changedParameter(0, root + 1n));
await expectRelationRejection('wrong public campaign', changedParameter(1, campaign + 1n));
await expectRelationRejection('wrong stored root', changedRead(3, root + 1n));
await expectRelationRejection('wrong stored campaign', changedRead(4, campaign + 1n));

let state = ledger.StateValue.newArray();
state = state.arrayPush(ledger.StateValue.newCell(field(root)));
state = state.arrayPush(ledger.StateValue.newCell(field(campaign)));
state = state.arrayPush(ledger.StateValue.newMap(new ledger.StateMap()));
const context = new ledger.QueryContext(new ledger.ChargedState(state), ledger.dummyContractAddress());
const cost = ledger.CostModel.initialCostModel();
const gatherOperations = operations.map(op => op.popeq ?
  { popeq: { ...op.popeq, result: null } } : op);
const gathered = context.query(gatherOperations, cost);
assert.deepEqual(gathered.events.filter(event => event.tag === 'read')
  .map(event => ledger.valueToBigInt(event.content.value)),
  [root, campaign, nullifier, root, campaign, 0n]);
const transcript = { gas: gathered.gasCost, effects: gathered.context.effects, program: operations };
const updated = context.runTranscript(transcript, cost);
const spentValue = updated.state.state.asArray()[2].asMap().get(field(nullifier));
assert.equal(ledger.valueToBigInt(spentValue.asCell().value), 1n);
assert.equal(context.state.state.asArray()[2].asMap().get(field(nullifier)), undefined,
  'the immutable initial state must stay unchanged');
assert.throws(() => updated.runTranscript(transcript, cost),
  /mismatch between expected .* and actual .* read/, 'native VM must reject nullifier replay');
assert.equal(ledger.valueToBigInt(updated.state.state.asArray()[2]
  .asMap().get(field(nullifier)).asCell().value), 1n);

console.log(JSON.stringify({
  relation: 'native-ledger-transcript', ledgerPackage: '1.0.2', zkirVersion: '3.2.0',
  k: relation.getK(), serializedBytes: relation.serialize().length,
  validPreprocessing: true, wrongSecretRejected: true,
  wrongPublicRootRejected: true, wrongPublicCampaignRejected: true,
  wrongStoredRootRejected: true, wrongStoredCampaignRejected: true,
  nativeStateUpdate: true, nativeReplayRejected: true,
  proofGenerated: false, ledgerTransactionSubmitted: false,
  checkerPublicInputGroups: accepted.length,
}, null, 2));
