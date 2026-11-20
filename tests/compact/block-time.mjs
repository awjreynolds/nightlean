import assert from 'node:assert/strict';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';

const [generatedDirectory] = process.argv.slice(2);
const runtimeDirectory = process.env.NOCTIUM_COMPACT_RUNTIME_DIR;
assert.ok(generatedDirectory && runtimeDirectory, 'pass the compiler output and set NOCTIUM_COMPACT_RUNTIME_DIR');
const { createCircuitContext, createConstructorContext, dummyContractAddress } = await import(
  pathToFileURL(resolve(runtimeDirectory, 'dist/index.js')).href,
);
const { Contract } = await import(
  pathToFileURL(resolve(generatedDirectory, 'contract/index.js')).href,
);

const contract = new Contract({});
const key = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, key));
for (const [time, cutoff] of [[9, 10n], [10, 10n], [11, 10n], [0, 0n], [0, (1n << 64n) - 1n]]) {
  for (const enabled of [true, false]) {
    const context = createCircuitContext({
      circuitId: 'checkTime',
      contractAddress: dummyContractAddress(),
      coinPublicKeyOrZswapState: key,
      contractState: currentContractState.data,
      privateState: null,
      time,
    });
    const { result } = await contract.circuits.checkTime(context, cutoff, enabled);
    assert.deepEqual(result, [enabled && BigInt(time) < cutoff, enabled && BigInt(time) > cutoff]);
  }
}
console.log('Compact 0.36.1 agreed with strict Unix-second predicates in all 10 cases');
