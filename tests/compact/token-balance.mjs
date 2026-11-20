import assert from 'node:assert/strict';
import {
  createCircuitContext, createConstructorContext, dummyContractAddress,
} from '@midnight-ntwrk/compact-runtime';
import { Contract } from './compact/contract/index.js';

const contract = new Contract({});
const key = '00'.repeat(32);
const color = Uint8Array.from({length: 32}, (_, i) => i + 1);
const raw = Buffer.from(color).toString('hex');
const max128 = (1n << 128n) - 1n;
const { currentContractState } = await contract.initialState(createConstructorContext(null, key));

function inspect(unshielded, shielded, tag, limit, enabled, exact) {
  const context = createCircuitContext({
    circuitId: 'inspect',
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: key,
    contractState: currentContractState.data,
    privateState: null,
  });
  const vm = context.callContext.currentQueryContext;
  const balance = new Map();
  balance.set({tag: 'unshielded', raw}, unshielded);
  if (shielded !== null) {
    balance.set({tag: 'shielded', raw}, shielded);
  }
  vm.block = {...vm.block, balance};
  return contract.circuits.inspect(context, color, tag, limit, enabled, exact);
}

for (const [shielded, tag, limit, enabled, exact, amount] of [
  [23n, true, 20n, true, true, 17n],
  [23n, false, 20n, true, true, 23n],
  [23n, false, 23n, true, true, 23n],
  [null, false, 20n, true, true, 0n],
  [max128, false, max128, false, true, max128],
  [max128, false, max128, false, false, max128],
]) {
  const {result} = await inspect(17n, shielded, tag, limit, enabled, exact);
  assert.deepEqual(result, [exact ? amount : 0n, enabled && amount < limit, enabled && amount > limit]);
}
for (const [amount, limit] of [[max128, 0n], [23n, max128]]) {
  await assert.rejects(async () => inspect(17n, amount, false, limit, true, false),
    /decode for built-in type u64/);
}
console.log('Token balance: six Compact results and two width rejections matched');
