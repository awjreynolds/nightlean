import assert from 'node:assert/strict';
import {createCircuitContext, createConstructorContext} from '@midnight-ntwrk/compact-runtime';
import {Contract} from './compact/contract/index.js';

const contract = new Contract({});
const key = '00'.repeat(32);
const color = Uint8Array.from({length: 32}, (_, index) => index + 1);
const recipient = new Uint8Array(32).fill(9);
const issuer = '09'.repeat(32);
const {currentContractState} = await contract.initialState(createConstructorContext(null, key));
const max64 = (1n << 64n) - 1n;
const max128 = (1n << 128n) - 1n;

function record(amount, extra, isUnshielded, isContract, enabled, addSecond) {
  const context = createCircuitContext({
    circuitId: 'record', contractAddress: issuer, coinPublicKeyOrZswapState: key,
    contractState: currentContractState.data, privateState: null,
  });
  return contract.circuits.record(context, color, amount, extra, isUnshielded, isContract, recipient, enabled, addSecond);
}

for (const [amount, extra, isUnshielded, isContract, enabled, addSecond, expected] of [
  [7n, 3n, true, true, true, true, 10n],
  [7n, 3n, false, false, false, true, 3n],
  [max128, 0n, false, true, true, false, max128],
  [7n, 3n, true, false, false, false, undefined],
]) {
  const {context} = await record(amount, extra, isUnshielded, isContract, enabled, addSecond);
  const effects = context.callContext.currentQueryContext.effects;
  const token = {tag: isUnshielded ? 'unshielded' : 'shielded', raw: Buffer.from(color).toString('hex')};
  const target = {tag: isContract ? 'contract' : 'user', address: issuer};
  const entries = expected === undefined ? [] : [[token, expected]];
  assert.deepEqual([...effects.unshieldedInputs], entries);
  assert.deepEqual([...effects.unshieldedOutputs], entries);
  assert.deepEqual([...effects.claimedUnshieldedSpends], expected === undefined ? [] : [[[token, target], expected]]);
}
for (const [amount, extra] of [[max64, 1n], [max128, 0n]]) {
  await assert.rejects(async () => record(amount, extra, true, true, true, true));
}
console.log('Tagged settlement: four Compact results and two width rejections matched');
