import assert from 'node:assert/strict';
import { createCircuitContext, createConstructorContext, dummyContractAddress } from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({});
const wallet = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
let state = currentContractState.data;

const call = (circuitId, value) => contract.circuits[circuitId](createCircuitContext({
  circuitId, contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: state, privateState: null,
}), value);

async function check(circuitId, value, shared, distinct) {
  const { context } = await call(circuitId, value);
  state = context.callContext.currentQueryContext.state;
  const cells = ledger(state);
  assert.deepEqual([cells.first_balance, cells.again_balance, cells.different_balance],
    [shared, shared, distinct]);
}

await check('first_update', 11n, 11n, 0n);
await check('againRead', 11n, 11n, 0n);
await check('again_update', 23n, 23n, 0n);
await check('different_update', 7n, 23n, 7n);
await assert.rejects(async () => call('againRead', 22n), /wrong shared balance/);
console.log('Compact module oracle passed: shared 23, distinct 7');
