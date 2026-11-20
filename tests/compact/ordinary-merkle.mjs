import assert from 'node:assert/strict';
import {createCircuitContext, createConstructorContext, dummyContractAddress} from '@midnight-ntwrk/compact-runtime';
import {Contract, ledger} from './compact/contract/index.js';

const contract = new Contract({});
const wallet = '00'.repeat(32);
const {currentContractState} = await contract.initialState(createConstructorContext(null, wallet));
let state = currentContractState.data;
const invoke = (entry, ...args) => contract.circuits[entry](createCircuitContext({
  circuitId: entry, contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: state, privateState: null,
}), ...args);
const roots = [];
for (let index = 0; index <= 4; index++) {
  const tree = ledger(state).claims;
  assert.equal(tree.firstFree(), BigInt(index));
  assert.equal((await invoke('fullStatus')).result, index === 4);
  roots.push(tree.root().field.toString());
  if (index < 4) {
    const append = await invoke('append', new Uint8Array(32).fill(index + 1));
    assert.equal(append.result, index === 3);
    state = append.context.callContext.currentQueryContext.state;
  }
}
await assert.rejects(async () => invoke('append', new Uint8Array(32).fill(5)));
const reset = await invoke('resetAndCheck');
assert.equal(reset.result, false);
const cleared = ledger(reset.context.callContext.currentQueryContext.state).claims;
assert.equal(cleared.firstFree(), 0n);
assert.equal(cleared.root().field.toString(), roots[0]);
console.log(JSON.stringify(roots));
