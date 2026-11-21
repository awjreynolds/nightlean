import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory] = process.argv.slice(2);
const runtimeDirectory = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generatedDirectory && runtimeDirectory, 'pass the generated directory and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
  pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href,
);
const { Contract, ledger } = await import(
  pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href,
);

const contract = new Contract({});
const walletKey = '00'.repeat(32);
const owner = new Uint8Array(32).fill(7);
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
const archiveSnapshot = () => {
  const tree = ledger(state).archives.lookup(owner);
  return {
    root: tree.root().field.toString(),
    firstFree: tree.firstFree().toString(),
    history: [...tree.history()].map(({ field }) => field.toString()).sort(),
  };
};

const historyRootSnapshot = () => {
  const tree = ledger(state).historyRoot;
  return {
    root: tree.root().field.toString(),
    firstFree: tree.firstFree().toString(),
    history: [...tree.history()].map(({ field }) => field.toString()).sort(),
  };
};

const ordinary = [];
assert.deepEqual(ordinarySnapshot(), { root: '0', firstFree: '0' });
await invoke('appendOrdinary', true);
ordinary.push(ordinarySnapshot());
await invoke('writeOrdinary', 3n, true);
ordinary.push(ordinarySnapshot());
await invoke('defaultOrdinary', 0n);
ordinary.push(ordinarySnapshot());
await assert.rejects(async () => invoke('writeOrdinary', 4n, true));
assert.deepEqual(ordinarySnapshot(), ordinary[2]);

const archives = [];
await invoke('insertDefaultArchive', owner);
const mapDefaultArchive = archiveSnapshot();
const mapDefaultHasZeroRoot = await invoke('archiveHasRoot', owner, { field: 0n });
assert.deepEqual(mapDefaultArchive, { root: '0', firstFree: '0', history: [] });
assert.equal(mapDefaultHasZeroRoot, false);
await invoke('setupArchive', owner);
const resetArchive = archiveSnapshot();
const resetArchiveHasZeroRoot = await invoke('archiveHasRoot', owner, { field: 0n });
assert.deepEqual(resetArchive.history, ['0']);
assert.equal(resetArchiveHasZeroRoot, true);

const rootHistoryInitial = historyRootSnapshot();
const rootHistoryHasZeroInitially = await invoke('rootHasRoot', { field: 0n });
await invoke('appendRootHistory', true);
const rootHistoryAfterAppend = historyRootSnapshot();
await invoke('resetHistoryRoot');
const rootHistoryAfterReset = historyRootSnapshot();
const rootHistoryHasZeroAfterReset = await invoke('rootHasRoot', { field: 0n });
assert.deepEqual(rootHistoryInitial.history, ['0']);
assert.deepEqual(rootHistoryAfterReset.history, ['0']);
assert.equal(rootHistoryHasZeroInitially, true);
assert.equal(rootHistoryHasZeroAfterReset, true);

await invoke('appendArchive', owner, true);
archives.push(archiveSnapshot());
await invoke('writeArchive', owner, 3n, true);
archives.push(archiveSnapshot());
await invoke('defaultArchive', owner, 0n);
archives.push(archiveSnapshot());
await assert.rejects(async () => invoke('writeArchive', owner, 4n, true));
assert.deepEqual(archiveSnapshot(), archives[2]);

assert.deepEqual(ordinary.map(({ firstFree }) => firstFree), ['1', '4', '4']);
assert.deepEqual(archives.map(({ root, firstFree }) => ({ root, firstFree })), ordinary);
assert.deepEqual(archives.map(({ history }, index) => history), archives.map((_, index) =>
  ['0', ...archives.slice(0, index + 1).map(({ root }) => root)].sort()));

console.log(JSON.stringify({
  ordinary,
  archives,
  historySemantics: {
    mapDefaultArchive,
    mapDefaultHasZeroRoot,
    resetArchive,
    resetArchiveHasZeroRoot,
    rootHistoryInitial,
    rootHistoryHasZeroInitially,
    rootHistoryAfterAppend,
    rootHistoryAfterReset,
    rootHistoryHasZeroAfterReset,
  },
}));
