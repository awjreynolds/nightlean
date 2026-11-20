import assert from 'node:assert/strict';
import { createCircuitContext, createConstructorContext, dummyContractAddress } from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({
  seed: ({ privateState }) => [[...privateState, 'seed'], 9n],
  empty: ({ privateState }, slot) => [[...privateState, Number(slot)], []],
  callback: () => assert.fail('empty iteration called its operator'),
});
const wallet = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext([], wallet));
const { result, context } = await contract.circuits.update(createCircuitContext({
  circuitId: 'update', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data, privateState: [],
}));
assert.equal(result, 9n);
assert.equal(ledger(context.callContext.currentQueryContext.state).total, 9n);
assert.deepEqual(context.callContext.currentPrivateState, ['seed', 1, 2, 3]);
console.log(JSON.stringify({ result: result.toString(), order: context.callContext.currentPrivateState }));
