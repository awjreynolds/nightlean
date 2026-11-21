import assert from 'node:assert/strict';
import { createCircuitContext, createConstructorContext, dummyContractAddress } from '@midnight-ntwrk/compact-runtime';
import { Contract } from './compact/contract/index.js';

const contract = new Contract({});
const wallet = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
const invoke = (thenCondition, elseCondition) => contract.circuits.branches(createCircuitContext({
  circuitId: 'branches',
  contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: wallet,
  contractState: currentContractState.data,
  privateState: null,
}), thenCondition, elseCondition, 3n);

assert.deepEqual((await invoke(false, true)).result, [true, true]);
await assert.rejects(invoke(true, true));
await assert.rejects(invoke(false, false));
