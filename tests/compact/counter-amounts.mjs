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
const owner = new Uint8Array(32).fill(4);
const spender = new Uint8Array(32).fill(7);
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

const [, seeded] = await invoke('seed', initial);
const [zero, same] = await invoke('apply', seeded, owner, spender, 0n);
assert.deepEqual(zero, [10n, 0n]);
const [increased, increasedState] = await invoke('apply', same, owner, spender, 3n);
assert.deepEqual(increased, [13n, 3n]);
const [reduced] = await invoke('reduce', increasedState, owner, spender, 2n);
assert.deepEqual(reduced, [11n, 1n]);
const [maximum] = await invoke('apply', initial, owner, spender, 65_535n);
assert.deepEqual(maximum, [65_535n, 65_535n]);
await assert.rejects(invoke('apply', initial, owner, spender, 65_536n));
await assert.rejects(invoke('reduce', initial, owner, spender, 1n));
const [, skipped] = await invoke('guarded', initial, owner, spender, 7n, false);
assert.equal(ledger(skipped).total, 0n);
assert.equal(ledger(skipped).epochs.member(owner), false);
await assert.rejects(invoke('guarded', initial, owner, spender, 7n, true));
console.log('Compact 0.36.1 passed the Counter amount comparison cases');
