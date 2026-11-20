import assert from 'node:assert/strict';
import { createCircuitContext, createConstructorContext, dummyContractAddress } from '@midnight-ntwrk/compact-runtime';
import { Contract, ledger } from './compact/contract/index.js';

const contract = new Contract({});
const wallet = '00'.repeat(32);
const { currentContractState } = await contract.initialState(createConstructorContext(null, wallet));
let state = currentContractState.data;
const invoke = (entry, ...args) => contract.circuits[entry](createCircuitContext({
  circuitId: entry, contractAddress: dummyContractAddress(), coinPublicKeyOrZswapState: wallet,
  contractState: state, privateState: null,
}), ...args);
const digest = byte => new Uint8Array(32).fill(byte);
const rows = [];
for (const [entry, index, value, cursor] of [
  ['writeHashIndex', 2n, digest(1), 3n],
  ['writeFieldIndex', 0n, 256n, 3n],
  ['writeHashIndex', 3n, digest(2), 4n],
  ['writeFieldIndex', 2n, 52435875175126190479447740508185965837690552500527637822603658699938581184512n, 4n],
  ['writeFieldIndex', 0n, 0n, 4n],
]) {
  const updated = await invoke(entry, index, value);
  state = updated.context.callContext.currentQueryContext.state;
  const tree = ledger(state).claims;
  assert.equal(tree.firstFree(), cursor);
  assert.equal(updated.result, cursor === 4n);
  rows.push({ cursor: Number(cursor), root: tree.root().field.toString() });
}
for (const index of [4n, (1n << 64n) - 1n]) {
  await assert.rejects(() => invoke('writeHashIndex', index, digest(3)));
}
console.log(JSON.stringify(rows));
