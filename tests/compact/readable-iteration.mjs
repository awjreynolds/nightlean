import assert from 'node:assert/strict';
import { createCircuitContext, createConstructorContext, dummyContractAddress } from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({
  iterationSeed: ({ privateState }) => [[...privateState, 'seed'], 7n],
  iterationBytes: ({ privateState }) => [[...privateState, 'bytes'], Uint8Array.from([4, 5])],
  iterationVisit: ({ privateState }, item) => [[...privateState, `visit:${item}`], item * 2n],
});
const wallet = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext([], wallet));
const { result, context } = await contract.circuits.update(createCircuitContext({
  circuitId: 'update', contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data, privateState: [],
}), 3n);
const total = ledger(context.callContext.currentQueryContext.state).total;
assert.equal(result, 31n);
assert.equal(total, 31n);
assert.deepEqual(context.callContext.currentPrivateState, ['seed', 'bytes', 'visit:4', 'visit:5']);
console.log(JSON.stringify({ result: result.toString(), total: total.toString(), order: context.callContext.currentPrivateState }));
