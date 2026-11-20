import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory] = process.argv.slice(2);
const runtimeDirectory = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generatedDirectory && runtimeDirectory, 'pass compiler output and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
  pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href,
);
const { Contract, ledger } = await import(
  pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href,
);

const contract = new Contract({});
const walletKey = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
const initial = currentContractState.data;
const bytesHex = (value) => Array.from(value, (byte) => byte.toString(16).padStart(2, '0')).join('');
const tagA = new Uint8Array(32).fill(7);
const tagB = new Uint8Array(32).fill(8);
const invoke = (state, bucket, tag, adding, removing, clearing) => contract.circuits.update(createCircuitContext({
  circuitId: 'update', contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
}), bucket, tag, adding, removing, clearing);
const transition = async (state, bucket, tag, adding = false, removing = false, clearing = false) => {
  const {result, context} = await invoke(state, bucket, tag, adding, removing, clearing);
  return [result, context.callContext.currentQueryContext.state];
};
const inspect = async (state, bucket, enabled) => (await contract.circuits.inspect(createCircuitContext({
  circuitId: 'inspect', contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: walletKey, contractState: state, privateState: null,
}), bucket, enabled)).result;
const members = (set) => [...set].map(bytesHex).sort((left, right) => left.localeCompare(right));
const snapshot = (state) => {
  const view = ledger(state);
  return {
    registered: members(view.registered),
    registeredSize: view.registered.size().toString(),
    groupOne: members(view.groups.lookup(1n)),
    groupOneSize: view.groups.lookup(1n).size().toString(),
    groupTwo: members(view.groups.lookup(2n)),
    groupTwoSize: view.groups.lookup(2n).size().toString(),
    groupCount: view.groups.size().toString(),
    isEmpty: view.registered.isEmpty(),
  };
};

assert.deepEqual(members(ledger(initial).registered), []);
assert.equal(ledger(initial).groups.member(1n), false);
assert.deepEqual(await inspect(initial, 1n, false), [true, true, false]);
await assert.rejects(() => inspect(initial, 1n, true));
let [result, state] = await transition(initial, 1n, tagA, true);
assert.deepEqual(result, [true, true, 1n, 1n, false]);
assert.deepEqual(await inspect(state, 1n, true), [false, false, false]);
[result, state] = await transition(state, 1n, tagA, true);
assert.deepEqual(result, [true, true, 1n, 1n, false]);
const afterDuplicate = {
  registered: members(ledger(state).registered),
  groupOne: members(ledger(state).groups.lookup(1n)),
};
assert.deepEqual(afterDuplicate, {registered: [bytesHex(tagA)], groupOne: [bytesHex(tagA)]});
[result, state] = await transition(state, 2n, tagB, true);
assert.deepEqual(result, [true, true, 2n, 1n, false]);
const afterSecondBucket = snapshot(state);
assert.deepEqual(await inspect(state, 1n, true), [false, false, false]);
assert.deepEqual(afterSecondBucket, {
  registered: [bytesHex(tagA), bytesHex(tagB)].sort((left, right) => left.localeCompare(right)),
  registeredSize: '2',
  groupOne: [bytesHex(tagA)], groupOneSize: '1',
  groupTwo: [bytesHex(tagB)], groupTwoSize: '1',
  groupCount: '2', isEmpty: false,
});
[result, state] = await transition(state, 1n, tagA, false, true);
assert.deepEqual(result, [false, false, 1n, 0n, false]);
const afterRemove = snapshot(state);
assert.deepEqual(afterRemove.registered, [bytesHex(tagB)]);
assert.deepEqual(afterRemove.groupOne, []);
assert.deepEqual(afterRemove.groupTwo, [bytesHex(tagB)]);
[result, state] = await transition(state, 1n, tagA, false, true);
assert.deepEqual(result, [false, false, 1n, 0n, false]);
assert.deepEqual(snapshot(state), afterRemove);
[result, state] = await transition(state, 1n, tagA, false, false, true);
assert.deepEqual(result, [false, false, 0n, 0n, true]);
const afterReset = snapshot(state);
assert.deepEqual(await inspect(state, 1n, true), [true, false, true]);
assert.deepEqual(afterReset, {
  registered: [], registeredSize: '0',
  groupOne: [], groupOneSize: '0',
  groupTwo: [bytesHex(tagB)], groupTwoSize: '1',
  groupCount: '2', isEmpty: true,
});
assert.equal(ledger(state).registered.member(tagA), false);
assert.equal(ledger(state).groups.lookup(2n).member(tagB), true);
console.log('Compact 0.36.1 matched the six Set transitions and guarded inspections');
