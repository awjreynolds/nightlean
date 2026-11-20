import assert from 'node:assert/strict';
import {
  createCircuitContext, createConstructorContext, dummyContractAddress,
} from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const calls = [];
const contract = new Contract({
  derive: ({ privateState }, before) => {
    calls.push(before);
    return [privateState, 7n];
  },
});
const key = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, key));
const context = (state) => createCircuitContext({
  circuitId: 'advance',
  contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: key,
  contractState: state,
  privateState: null,
});
let state = currentContractState.data;
for (const [outer, inner, bound, expected, mark, providers] of [
  [true, true, 7n, 10n, 1n, [3n]],
  [true, false, 8n, 999n, 2n, []],
  [false, true, 8n, 999n, 3n, []],
]) {
  calls.length = 0;
  const result = await contract.circuits.advance(context(state), outer, inner, bound, expected);
  state = result.context.callContext.currentQueryContext.state;
  assert.equal(result.result, 10n);
  assert.equal(ledger(state).balance, 10n);
  assert.equal(ledger(state).mark, mark);
  assert.deepEqual(calls, providers);
}
await assert.rejects(async () => contract.circuits.advance(
  context(currentContractState.data), true, true, 8n, 10n,
), /active narrowing check/);
await assert.rejects(async () => contract.circuits.advance(
  context(currentContractState.data), true, true, 7n, 999n,
), /active balance assertion/);

console.log('Compact 0.36.1 matched the three branch transitions, callback order and two active failures');
