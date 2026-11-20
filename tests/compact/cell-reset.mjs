import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const generatedDirectory = process.argv[2];
assert.ok(generatedDirectory, 'pass the compactc output directory');
const runtimePackage = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(runtimePackage, 'set NOCTIUM_COMPACT_RUNTIME_DIR to compact-runtime 0.21.0');
const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
  pathToFileURL(resolve(runtimePackage, 'dist/index.js')).href,
);
const { Contract, ledger } = await import(
  pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href,
);

const contract = new Contract({});
const key = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, key));
const context = (circuitId, state) => createCircuitContext({
  circuitId,
  contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: key,
  contractState: state,
  privateState: null,
});

for (const enabled of [true, false]) {
  const seeded = await contract.circuits.seed(context('seed', currentContractState.data));
  const before = ledger(seeded.context.callContext.currentQueryContext.state);
  assert.equal(before.amount, 42n);
  assert.equal(before.nonce, 17n);
  assert.equal(before.active, true);
  assert.deepEqual([...before.memo], [115, 101, 101, 100]);

  const { result, context: after } = await contract.circuits.clear(
    context('clear', seeded.context.callContext.currentQueryContext.state),
    enabled,
  );
  const values = ledger(after.callContext.currentQueryContext.state);
  assert.deepEqual([...result.slice(0, 3), [...result[3]]], enabled
    ? [0n, 0n, false, [0, 0, 0, 0]]
    : [42n, 17n, true, [115, 101, 101, 100]]);
  assert.deepEqual(values, enabled
    ? { amount: 0n, nonce: 0n, active: false, memo: new Uint8Array(4) }
    : { amount: 42n, nonce: 17n, active: true, memo: Uint8Array.from([115, 101, 101, 100]) });
}

console.log('Compact 0.36.1 reset default values and preserved the seeded state when the guard was false');
