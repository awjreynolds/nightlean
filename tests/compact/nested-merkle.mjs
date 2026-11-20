import assert from 'node:assert/strict';
import {
  createCircuitContext, createConstructorContext, dummyContractAddress,
} from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({});
const walletKey = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
let state = currentContractState.data;
const owner = (byte) => new Uint8Array(32).fill(byte);
const invoke = (entrypoint, ...args) => contract.circuits[entrypoint](createCircuitContext({
  circuitId: entrypoint, contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
}), ...args);
const apply = async (entrypoint, ...args) => {
  state = (await invoke(entrypoint, ...args)).context.callContext.currentQueryContext.state;
};
const check = async (path, field, expected) => {
  assert.deepEqual((await invoke('readTrees', ...path, {field})).result, expected);
};
const pathSnapshot = (path) => path === undefined ? null : ({
  leaf: path.leaf.toString(),
  path: path.path.map(({sibling, goes_left}) => ({
    sibling: sibling.field.toString(), goes_left,
  })),
});
const pathDigest = async (path) => (await invoke('digestFromPath', path)).result;
const sortedHistory = (tree) => [...tree.history()].map(({field}) => field)
  .sort((left, right) => left < right ? -1 : left > right ? 1 : 0).map(String);
const snapshot = ([address, bucket]) => {
  const view = ledger(state);
  const ordinary = view.ordinary.lookup(address).lookup(bucket);
  const archives = view.archives.lookup(address).lookup(bucket);
  return {
    ordinary: {
      firstFree: ordinary.firstFree().toString(),
      root: ordinary.root().field.toString(),
      fieldZeroPath: pathSnapshot(ordinary.findPathForLeaf(0n)),
    },
    archives: {
      firstFree: archives.firstFree().toString(),
      root: archives.root().field.toString(),
      fieldOnePath: pathSnapshot(archives.findPathForLeaf(1n)),
      history: sortedHistory(archives),
    },
  };
};

const a = [owner(7), 1n];
const sibling = [owner(7), 2n];
const other = [owner(8), 1n];
await assert.rejects(async () => invoke('readTrees', ...a, {field: 0n}));
await assert.rejects(async () => invoke('resetTrees', ...a));
for (const path of [a, sibling, other]) await apply('setup', ...path);
assert.equal(ledger(state).archives.lookup(a[0]).lookup(a[1]).findPathForLeaf(1n), undefined);
await apply('append', ...a, owner(1), 1n);
await apply('append', ...sibling, owner(2), 256n);
await apply('append', ...other, owner(4), 257n);
const afterAppend = snapshot(a);
const siblings = [snapshot(sibling), snapshot(other)];
const archivesPath = ledger(state).archives.lookup(a[0]).lookup(a[1]).findPathForLeaf(1n);
assert.ok(archivesPath);
assert.deepEqual(archivesPath, ledger(state).archives.lookup(a[0]).lookup(a[1]).pathForLeaf(0n, 1n));
assert.equal(await pathDigest(archivesPath), BigInt(afterAppend.archives.root));
assert.equal(ledger(state).archives.lookup(a[0]).lookup(a[1]).findPathForLeaf(999n), undefined);
const wrongArchivesPath = ledger(state).archives.lookup(a[0]).lookup(a[1]).pathForLeaf(0n, 999n);
const wrongArchivesRoot = await pathDigest(wrongArchivesPath);
assert.notEqual(wrongArchivesRoot, BigInt(afterAppend.archives.root));
await apply('setIndex', ...a, owner(3), 0n);
const afterIndexed = snapshot(a);
assert.deepEqual([afterIndexed.ordinary.firstFree, afterIndexed.archives.firstFree], ['3', '4']);
await check(a, BigInt(afterAppend.archives.root), [false, true, false, true]);
await check(a, BigInt(afterIndexed.ordinary.root), [true, false, false, true]);
const ordinaryPath = ledger(state).ordinary.lookup(a[0]).lookup(a[1]).findPathForLeaf(0n);
assert.ok(ordinaryPath);
assert.deepEqual(ordinaryPath, ledger(state).ordinary.lookup(a[0]).lookup(a[1]).pathForLeaf(2n, 0n));
assert.equal(await pathDigest(ordinaryPath), BigInt(afterIndexed.ordinary.root));
assert.equal(ledger(state).ordinary.lookup(a[0]).lookup(a[1]).findPathForLeaf(999n), undefined);
const wrongOrdinaryPath = ledger(state).ordinary.lookup(a[0]).lookup(a[1]).pathForLeaf(2n, 999n);
const wrongOrdinaryRoot = await pathDigest(wrongOrdinaryPath);
assert.notEqual(wrongOrdinaryRoot, BigInt(afterIndexed.ordinary.root));
const archiveAtIndex = ledger(state).archives.lookup(a[0]).lookup(a[1]).pathForLeaf(0n, 999n);
const archiveCandidateRoot = await pathDigest(archiveAtIndex);
const ordinaryAtCursor = ledger(state).ordinary.lookup(a[0]).lookup(a[1]).pathForLeaf(3n, 777n);
const indexedCursorRoot = await pathDigest(ordinaryAtCursor);
await apply('clear', ...a);
const afterClear = snapshot(a);
assert.deepEqual(afterClear.ordinary, afterIndexed.ordinary);
assert.equal(afterClear.archives.root, afterIndexed.archives.root);
assert.equal(afterClear.archives.firstFree, afterIndexed.archives.firstFree);
assert.deepEqual(afterClear.archives.history, [afterIndexed.archives.root]);
await check(a, BigInt(afterAppend.archives.root), [false, false, false, true]);
await check(a, BigInt(afterIndexed.archives.root), [false, true, false, true]);
assert.deepEqual([snapshot(sibling), snapshot(other)], siblings);
await check(sibling, 0n, [false, true, false, false]);
await apply('resetTrees', ...a);
const afterReset = snapshot(a);
assert.deepEqual(afterReset.ordinary, {
  firstFree: '0', root: '0', fieldZeroPath: null,
});
assert.deepEqual(afterReset.archives, {
  firstFree: '0', root: '0', fieldOnePath: null, history: ['0'],
});
await check(a, 0n, [true, true, false, false]);
assert.deepEqual([snapshot(sibling), snapshot(other)], siblings);

const ordinary = () => ledger(state).ordinary.lookup(a[0]).lookup(a[1]);
assert.throws(() => ordinary().pathForLeaf(0n, 777n));
await apply('setIndex', ...a, owner(3), 0n);
assert.equal(ordinary().firstFree(), 3n);
assert.throws(() => ordinary().pathForLeaf(1n, 777n));
assert.equal(ordinary().pathForLeaf(2n, 777n).leaf, 777n);
const atCursor = ordinary().pathForLeaf(3n, 777n);
assert.equal(atCursor.leaf, 777n);
assert.throws(() => ordinary().pathForLeaf(4n, 777n));
const paths = {
  wrongArchives: {root: wrongArchivesRoot.toString(), path: pathSnapshot(wrongArchivesPath)},
  wrongOrdinary: {root: wrongOrdinaryRoot.toString(), path: pathSnapshot(wrongOrdinaryPath)},
  archiveAfterIndex: {root: archiveCandidateRoot.toString(), path: pathSnapshot(archiveAtIndex)},
  cursorAfterIndex: {root: indexedCursorRoot.toString(), path: pathSnapshot(ordinaryAtCursor)},
  atCursor: {root: (await pathDigest(atCursor)).toString(), path: pathSnapshot(atCursor)},
};
console.log(JSON.stringify({afterAppend, afterIndexed, afterClear, afterReset, siblings, paths}));
