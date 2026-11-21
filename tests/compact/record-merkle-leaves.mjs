import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory] = process.argv.slice(2);
const runtimeDirectory = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generatedDirectory && runtimeDirectory, 'pass the generated directory and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, dummyContractAddress, leafHash: runtimeLeafHash } = await import(
  pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href,
);
const { Contract, ledger } = await import(
  pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href,
);

const contract = new Contract({});
const walletKey = '00'.repeat(32);
const leaf = { tag: new Uint8Array([12, 0, 0]), approved: true, count: 258n };
const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
let state = currentContractState.data;

const invoke = async (entrypoint, ...args) => {
  const context = createCircuitContext({
    circuitId: entrypoint,
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: state,
    privateState: null,
  });
  const call = await contract.circuits[entrypoint](context, ...args);
  state = call.context.callContext.currentQueryContext.state;
  return call.result;
};

const ordinarySnapshot = () => {
  const tree = ledger(state).ordinary;
  return { root: tree.root().field.toString(), firstFree: tree.firstFree().toString() };
};
const historySnapshot = () => {
  const tree = ledger(state).history;
  return {
    root: tree.root().field.toString(),
    firstFree: tree.firstFree().toString(),
    history: [...tree.history()].map(({ field }) => field.toString()).sort(),
  };
};

const ordinary = [];
assert.deepEqual(ordinarySnapshot(), { root: '0', firstFree: '0' });
await invoke('appendOrdinary', leaf);
ordinary.push(ordinarySnapshot());
await invoke('writeOrdinary', 3n, leaf);
ordinary.push(ordinarySnapshot());
await invoke('defaultOrdinary', 0n);
ordinary.push(ordinarySnapshot());
await assert.rejects(async () => invoke('writeOrdinary', 4n, leaf));
assert.deepEqual(ordinarySnapshot(), ordinary[2]);

const historic = [];
assert.deepEqual(historySnapshot(), { root: '0', firstFree: '0', history: ['0'] });
await invoke('appendHistoric', leaf);
historic.push(historySnapshot());
await invoke('writeHistoric', 3n, leaf);
historic.push(historySnapshot());
await invoke('defaultHistoric', 0n);
historic.push(historySnapshot());
await assert.rejects(async () => invoke('writeHistoric', 4n, leaf));
assert.deepEqual(historySnapshot(), historic[2]);

assert.deepEqual(ordinary.map(({ firstFree }) => firstFree), ['1', '4', '4']);
assert.deepEqual(historic.map(({ root, firstFree }) => ({ root, firstFree })), ordinary);
assert.deepEqual(historic.map(({ history }, index) => history), historic.map((_, index) =>
  ['0', ...historic.slice(0, index + 1).map(({ root }) => root)].sort()));

const leafEncoding = Buffer.from([12, 0, 0, 1, 2, 1]);
const defaultEncoding = Buffer.alloc(6);
const recordAlignment = [3, 1, 2].map((length) => ({ tag: 'atom', value: { tag: 'bytes', length } }));
const hashAlignedRecord = (value) => Buffer.from(runtimeLeafHash({ value, alignment: recordAlignment }).value[0]).toString('hex');
const leafDigest = createHash('sha256').update('mdn:lh').update(leafEncoding).digest('hex');
const defaultDigest = createHash('sha256').update('mdn:lh').update(defaultEncoding).digest('hex');
assert.equal(hashAlignedRecord([Uint8Array.of(12), Uint8Array.of(1), Uint8Array.from([2, 1])]), leafDigest);
assert.equal(hashAlignedRecord([new Uint8Array(), new Uint8Array(), new Uint8Array()]), defaultDigest);

console.log(JSON.stringify({
  ordinary,
  historic,
  encoding: {
    leaf: leafEncoding.toString('hex'),
    leafHash: leafDigest,
    default: defaultEncoding.toString('hex'),
    defaultHash: defaultDigest,
  },
}));
