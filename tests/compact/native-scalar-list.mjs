import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory] = process.argv.slice(2);
const runtimeDirectory = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generatedDirectory && runtimeDirectory, 'pass compiler output and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
  pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href,
);
const { Contract } = await import(
  pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href,
);

const contract = new Contract({});
const walletKey = '00'.repeat(32);
const owner = new Uint8Array(32).fill(7);
const first = Uint8Array.from({ length: 128 }, (_, index) => index);
const second = Uint8Array.from({ length: 128 }, (_, index) => index + 128);
const zero = new Uint8Array(128);
const { currentContractState } = await contract.initialState(createConstructorContext(null, walletKey));
const initial = currentContractState.data;
const invoke = async (name, state, ...args) => {
  const context = createCircuitContext({
    circuitId: name,
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: walletKey,
    contractState: state,
    privateState: null,
  });
  const call = await contract.circuits[name](context, ...args);
  return [call.result, call.context.callContext.currentQueryContext.state];
};
const expectView = async (state, length, value, memo) => {
  const empty = length === 0n;
  const [result] = await invoke('inspect', state, owner, true);
  assert.deepEqual(result, [length, empty, !empty, value, length, empty, !empty, memo]);
};

const [inactive] = await invoke('inspect', initial, owner, false);
assert.deepEqual(inactive, [0n, false, false, 0n, 0n, false, false, zero]);
const [, empty] = await invoke('reset', initial, owner);
await expectView(empty, 0n, 0n, zero);
const [, one] = await invoke('push', empty, owner, 5n, first);
await expectView(one, 1n, 5n, first);
const [, two] = await invoke('push', one, owner, 300n, second);
await expectView(two, 2n, 300n, second);
const [, popped] = await invoke('pop', two, owner);
await expectView(popped, 1n, 5n, first);
const [, reset] = await invoke('reset', popped, owner);
await expectView(reset, 0n, 0n, zero);
console.log('Compact 0.36.1 passed the Field and Bytes128 List comparison cases');
