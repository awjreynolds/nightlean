import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory] = process.argv.slice(2);
const runtimeDirectory = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generatedDirectory && runtimeDirectory, 'pass compiler output and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
  pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href,
);
const { Contract, ledger } = await import(pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href);
const contract = new Contract({});
const key = '00'.repeat(32);
const bytes = Uint8Array.from({length: 32}, (_, index) => index + 1);
const zero = new Uint8Array(32);
const address = Buffer.from(bytes).toString('hex');
const { currentContractState } = await contract.initialState(createConstructorContext(null, key));
let state = currentContractState.data;
for (const tag of ['contract', 'user', undefined]) {
  for (const enabled of [true, false]) {
    const recorded = ledger(state).recorded;
    const context = createCircuitContext({
      circuitId: 'lookup', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: key,
      contractState: state, privateState: null,
    });
    if (tag) {
      const vm = context.callContext.currentQueryContext;
      vm.block = {...vm.block, caller: {tag, address}};
    }
    const { result, context: after } = await contract.circuits.lookup(context, enabled);
    state = after.callContext.currentQueryContext.state;
    assert.equal(result.is_some, enabled && tag !== undefined);
    assert.equal(result.value.is_left, enabled && tag === 'contract');
    assert.deepEqual(result.value.left.bytes, enabled && tag === 'contract' ? bytes : zero);
    assert.deepEqual(result.value.right.bytes, enabled && tag === 'user' ? bytes : zero);
    assert.equal(ledger(state).recorded, enabled ? tag !== undefined : recorded);
  }
}
console.log('Compact 0.36.1 matched absent, contract and user callers in both guard branches');
