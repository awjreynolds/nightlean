import assert from 'node:assert/strict';
import {
  createCircuitContext, createConstructorContext, dummyContractAddress,
} from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({});
const walletKey = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
let state = currentContractState.data;
const owner = byte => new Uint8Array(32).fill(byte);
const invoke = (entry, ...args) => contract.circuits[entry](createCircuitContext({
  circuitId: entry, contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: walletKey,
  contractState: state, privateState: null,
}), ...args);
const apply = async (entry, ...args) => {
  state = (await invoke(entry, ...args)).context.callContext.currentQueryContext.state;
};
const check = async (path, field, expected) =>
  assert.deepEqual((await invoke('readTrees', ...path, {field})).result, expected);
const snapshot = ([address, bucket]) => {
  const view = ledger(state);
  const ordinary = view.ordinary.lookup(address).lookup(bucket);
  const archives = view.archives.lookup(address).lookup(bucket);
  const tree = value => [value.firstFree().toString(), value.root().field.toString()];
  const history = [...archives.history()].map(({field}) => field.toString()).sort();
  return {ordinary: tree(ordinary), archives: tree(archives), history};
};

const a = [owner(7), 1n];
const sibling = [owner(7), 2n];
const other = [owner(8), 1n];
await assert.rejects(async () => invoke('readTrees', ...a, {field: 0n}));
await assert.rejects(async () => invoke('resetTrees', ...a));
await apply('setupAndAppend', ...a, owner(1), 1n);
const afterAppend = snapshot(a);
for (const path of [sibling, other]) await apply('setup', ...path);
assert.deepEqual(snapshot(a), afterAppend);
await apply('append', ...sibling, owner(2), 256n);
await apply('append', ...other, owner(4), 257n);
const siblings = [snapshot(sibling), snapshot(other)];

await apply('setIndex', ...a, owner(3), 0n, 3n);
const afterIndexed = snapshot(a);
assert.deepEqual([afterIndexed.ordinary[0], afterIndexed.archives[0]], ['3', '4']);
await check(a, BigInt(afterAppend.archives[1]), [false, true, false, true]);
await check(a, BigInt(afterIndexed.ordinary[1]), [true, false, false, true]);
await assert.rejects(async () => invoke('setIndex', ...a, owner(4), 1n, 4n));
assert.deepEqual(snapshot(a), afterIndexed);
await apply('setIndex', ...a, owner(5), 256n, 3n);
const afterReplacement = snapshot(a);
assert.deepEqual([afterReplacement.ordinary[0], afterReplacement.archives[0]], ['3', '4']);
assert.notEqual(afterReplacement.archives[1], afterIndexed.archives[1]);
await check(a, BigInt(afterIndexed.archives[1]), [false, true, false, true]);

await apply('clear', ...a);
const afterClear = snapshot(a);
assert.deepEqual(afterClear, {...afterReplacement, history: [afterReplacement.archives[1]]});
await check(a, BigInt(afterAppend.archives[1]), [false, false, false, true]);
await check(a, BigInt(afterReplacement.archives[1]), [false, true, false, true]);
assert.deepEqual([snapshot(sibling), snapshot(other)], siblings);
await apply('resetTrees', ...a);
const afterReset = snapshot(a);
assert.deepEqual(afterReset, {ordinary: ['0', '0'], archives: ['0', '0'], history: ['0']});
await check(a, 0n, [true, true, false, false]);
assert.deepEqual([snapshot(sibling), snapshot(other)], siblings);
console.log(JSON.stringify({afterAppend, afterIndexed, afterReplacement, afterClear, afterReset, siblings}));
