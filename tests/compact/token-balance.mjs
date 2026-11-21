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

function contextWithBalance(circuitId, unshielded, shielded) {
  const context = createCircuitContext({
    circuitId,
    contractAddress: dummyContractAddress(),
    coinPublicKeyOrZswapState: key,
    contractState: currentContractState.data,
    privateState: null,
  });
  const vm = context.callContext.currentQueryContext;
  const balance = new Map();
  if (unshielded !== null) {
    balance.set({tag: 'unshielded', raw}, unshielded);
  }
  if (shielded !== null) {
    balance.set({tag: 'shielded', raw}, shielded);
  }
  vm.block = {...vm.block, balance};
  return context;
}

function inspect(unshielded, shielded, tag, limit, enabled, exact) {
  return contract.circuits.inspect(
    contextWithBalance('inspect', unshielded, shielded), color, tag, limit, enabled, exact,
  );
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

for (const [amount, expected] of [
  [17n, [17n, true, false, false, true]],
  [20n, [20n, false, true, false, true]],
  [23n, [23n, false, true, true, false]],
  [null, [0n, true, false, false, true]],
]) {
  const context = contextWithBalance('unshielded', amount, 11n);
  const {result} = await contract.circuits.unshielded(context, color, 20n, true);
  assert.deepEqual(result, expected);
}
const inactive = await contract.circuits.unshielded(
  contextWithBalance('unshielded', max128, 11n), color, max128, false,
);
assert.deepEqual(inactive.result, [max128, false, false, false, false]);
await assert.rejects(async () => contract.circuits.unshielded(
  contextWithBalance('unshielded', max128, 11n), color, 20n, true,
), /decode for built-in type u64/);
console.log('Unshielded helpers: five Compact results and one width rejection matched');
