import assert from 'node:assert/strict';
import {createCircuitContext, createConstructorContext} from '@midnight-ntwrk/compact-runtime';
import {Contract} from './compact/contract/index.js';

const contract = new Contract({});
const key = '00'.repeat(32);
const domain = Uint8Array.from({length: 32}, (_, index) => index + 1);
const rawDomain = Buffer.from(domain).toString('hex');
const max64 = (1n << 64n) - 1n;
const {currentContractState} = await contract.initialState(createConstructorContext(null, key));

function record(amount, enabled, addSecond) {
  const context = createCircuitContext({
    circuitId: 'record',
    contractAddress: '09'.repeat(32),
    coinPublicKeyOrZswapState: key,
    contractState: currentContractState.data,
    privateState: null,
  });
  return contract.circuits.record(context, domain, amount, enabled, addSecond);
}

for (const [amount, enabled, addSecond, expected] of [
  [17n, true, true, 19n],
  [max64, true, false, max64],
  [17n, false, true, 2n],
  [17n, false, false, undefined],
]) {
  const {context} = await record(amount, enabled, addSecond);
  const effects = context.callContext.currentQueryContext.effects;
  const entries = expected === undefined ? [] : [[rawDomain, expected]];
  assert.deepEqual([...effects.shieldedMints], entries);
  assert.deepEqual([...effects.unshieldedMints], entries);
  assert.equal(effects.unshieldedInputs.size, 0);
  assert.equal(effects.unshieldedOutputs.size, 0);
  assert.equal(effects.claimedUnshieldedSpends.size, 0);
}
await assert.rejects(async () => record(max64, true, true), /overflow/i);
console.log('Standalone mints: four Compact results and accumulated overflow matched');
