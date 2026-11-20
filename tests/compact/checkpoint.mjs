import assert from 'node:assert/strict';
import { createCircuitContext, createConstructorContext, dummyContractAddress } from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({});
const key = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, key));
const context = () => createCircuitContext({
  circuitId: 'apply', contractAddress: dummyContractAddress(),
  coinPublicKeyOrZswapState: key, contractState: currentContractState.data, privateState: null,
});
for (const enabled of [true, false]) {
  const { result, context: after } = await contract.circuits.apply(context(), enabled);
  assert.equal(result, 2n);
  const values = ledger(after.callContext.currentQueryContext.state);
  assert.equal(values.firstMark, 1n);
  assert.equal(values.secondMark, 2n);
  assert.equal(after.callProofDataTrace.at(-1).publicTranscript.filter((value) => value === 'ckpt').length, Number(enabled));
}
console.log('Compact 0.36.1 matched state, return and guarded checkpoint presence');
