import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory] = process.argv.slice(2);
const runtimeDirectory = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generatedDirectory && runtimeDirectory, 'pass compiler output and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, encodeContractAddress } = await import(
  pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href,
);
const { Contract, ledger } = await import(pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href);

const contract = new Contract({});
const key = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, key));
let state = currentContractState.data;
const cases = [Uint8Array.from({length:32}, (_, index) => index), new Uint8Array(32).fill(255)];
for (const address of cases) {
  const hex = Buffer.from(address).toString('hex');
  assert.deepEqual(encodeContractAddress(hex), address);
  for (const enabled of [true, false]) {
    const before = ledger(state).lastAddress;
    const invocation = createCircuitContext({
      circuitId: 'identify', contractAddress: hex, coinPublicKeyOrZswapState: key,
      contractState: state, privateState: null,
    });
    const { result, context } = await contract.circuits.identify(invocation, enabled);
    state = context.callContext.currentQueryContext.state;
    assert.deepEqual(result, enabled ? address : new Uint8Array(32));
    assert.deepEqual(ledger(state).lastAddress, enabled ? address : before);
  }
}
console.log('Compact 0.36.1 matched both address reads and both guarded skips');
